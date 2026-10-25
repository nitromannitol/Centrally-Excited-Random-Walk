module

public import CERW.Support.Outer.Radius.PlanarBracket

@[expose] public section

/-!
# Planar Scales

The planar radius and logarithms determine the scales of the exterior argument. The global
approximation then gives the first potential bound in the annulus.
The retained labels `eq:planar-exterior-pointwise`
refer to the earlier source `paper/limit-shapes.tex`.
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

/-- The planar scales: with `q = √(lg/r)` and `σ = q^{1/2}`, `σ ≥ 0`, `σ² = q`, `r σ⁴ = lg` and
`r q = √(r lg)`. -/
lemma pl_scales {r lg : ℝ} (hr : 0 < r) (hlg : 0 ≤ lg) :
    0 ≤ Real.sqrt (lg / r) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) ∧
    (Real.sqrt (lg / r) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) ^ 2 = Real.sqrt (lg / r) ∧
    r * (Real.sqrt (lg / r) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) ^ 4 = lg ∧
    r * Real.sqrt (lg / r) = Real.sqrt (r * lg) := by
  have hq : 0 ≤ Real.sqrt (lg / r) := Real.sqrt_nonneg _
  have hσ : Real.sqrt (lg / r) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) =
      Real.sqrt (Real.sqrt (lg / r)) := by
    rw [Real.sqrt_eq_rpow (Real.sqrt _)]
    norm_num
  rw [hσ]
  have h2 : Real.sqrt (Real.sqrt (lg / r)) ^ 2 = Real.sqrt (lg / r) := Real.sq_sqrt hq
  have h4 : Real.sqrt (lg / r) ^ 2 = lg / r := Real.sq_sqrt (div_nonneg hlg hr.le)
  refine ⟨Real.sqrt_nonneg _, h2, ?_, ?_⟩
  · calc r * Real.sqrt (Real.sqrt (lg / r)) ^ 4
        = r * (Real.sqrt (Real.sqrt (lg / r)) ^ 2) ^ 2 := by ring
      _ = lg := by
          rw [h2, h4]
          field_simp
  · have e : r * lg = r ^ 2 * (lg / r) := by
      field_simp
    rw [e, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]

/-- `√(√x) = x^{1/4}` for `x ≥ 0`. -/
lemma pl_sqrt_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) = x ^ ((1 : ℝ) / 4) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num

/-- `(K P w)^{1/2} ≤ K P^{1/2} w^{1/2}` for `K ≥ 1` and `P ≥ 0`. -/
lemma pl_rpow_half_le {K P w : ℝ} (hK : 1 ≤ K) (hP : 0 ≤ P) :
    (K * P * w ^ (2 - 1)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) ≤
      K * (Real.sqrt P * Real.sqrt w) := by
  have e : (K * P * w ^ (2 - 1)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) = Real.sqrt (K * P * w) := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), mul_assoc]
  have hK' : Real.sqrt K ≤ K := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  exact mul_le_mul_of_nonneg_right hK' (by positivity)

/-- `log(x + 2) ≤ 2 log x` and `log(4x + 2) ≤ 2 log x` for `x ≥ 16`. -/
lemma pl_logs {x : ℝ} (hx : 16 ≤ x) :
    Real.log (x + 2) ≤ 2 * Real.log x ∧ Real.log (4 * x + 2) ≤ 2 * Real.log x := by
  have h2 : 2 * Real.log x = Real.log (x ^ 2) := by
    rw [Real.log_pow]
    norm_num
  rw [h2]
  constructor <;> exact Real.log_le_log (by linarith) (by nlinarith)

/-- The numerical consequences of the scale bounds: with `r σ⁴ = lg`, `lg⁵ ≤ θ⁴ r`,
`P = r σ²` and `|b - r| ≤ C P`, we get `σ lg ≤ θ`, `σ ≤ 1`, `3r/4 ≤ b ≤ 5r/4` and
`lg ≤ P ≤ r`. -/
lemma pl_numeric {θ Ci r lg σ b P : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hCi0 : 0 ≤ Ci)
    (hθCi : Ci * θ ≤ 1) (hlg4 : 4 ≤ lg) (hr0 : 0 < r) (hσ0 : 0 ≤ σ) (hσ4 : r * σ ^ 4 = lg)
    (hlg5 : lg ^ 5 ≤ θ ^ 4 * r) (hP : P = r * σ ^ 2) (hbr : |b - r| ≤ Ci * P) :
    σ * lg ≤ θ ∧ σ ≤ 1 ∧ 3 * r / 4 ≤ b ∧ b ≤ 5 * r / 4 ∧ P ≤ r ∧ lg ≤ P := by
  have hσlg : σ * lg ≤ θ := by
    have h1 : (σ * lg) ^ 4 * r ≤ θ ^ 4 * r := by
      calc (σ * lg) ^ 4 * r = (r * σ ^ 4) * lg ^ 4 := by ring
        _ = lg ^ 5 := by rw [hσ4]; ring
        _ ≤ θ ^ 4 * r := hlg5
    have h2 : (σ * lg) ^ 4 ≤ θ ^ 4 := le_of_mul_le_mul_right h1 hr0
    exact (pow_le_pow_iff_left₀ (mul_nonneg hσ0 (by linarith)) hθ0.le four_ne_zero).mp h2
  have hσ4' : 4 * σ ≤ θ := by
    have := mul_le_mul_of_nonneg_left hlg4 hσ0
    linarith
  have hσ1 : σ ≤ 1 := by linarith
  have hCiσ2 : Ci * σ ^ 2 ≤ 1 / 4 := by
    have h1 : Ci * σ ≤ 1 / 4 := by
      have := mul_le_mul_of_nonneg_left hσ4' hCi0
      linarith
    calc Ci * σ ^ 2 = (Ci * σ) * σ := by ring
      _ ≤ (1 / 4) * 1 := mul_le_mul h1 hσ1 hσ0 (by norm_num)
      _ = 1 / 4 := by ring
  have hCiP : Ci * P ≤ r / 4 := by
    rw [hP]
    calc Ci * (r * σ ^ 2) = r * (Ci * σ ^ 2) := by ring
      _ ≤ r * (1 / 4) := by gcongr
      _ = r / 4 := by ring
  have hσsq : σ ^ 2 ≤ 1 := pow_le_one₀ hσ0 hσ1
  refine ⟨hσlg, hσ1, by linarith [(abs_le.mp hbr).1], by linarith [(abs_le.mp hbr).2], ?_, ?_⟩
  · rw [hP]
    calc r * σ ^ 2 ≤ r * 1 := by gcongr
      _ = r := mul_one r
  · rw [hP, ← hσ4]
    have : σ ^ 4 ≤ σ ^ 2 := by
      calc σ ^ 4 = σ ^ 2 * σ ^ 2 := by ring
        _ ≤ σ ^ 2 * 1 := by gcongr
        _ = σ ^ 2 := mul_one _
    gcongr

/-- Beyond the inner ball the potentials of `D_n` and of `E = D_n ∖ B(0, b)` agree
(`eq:ballpotential-euclid`). -/
lemma pl_split {ε : ℝ} (Y : ℕ → Site 2) (n : ℕ) {b : ℝ} (hb : innerRadius Y n = b)
    (hb0 : 0 < b) {y : EuclideanSpace ℝ (Fin 2)} (hy : b ≤ ‖y‖) :
    potential 2 ε (cellSet Y n) y = potential 2 ε (cellSet Y n \ Metric.ball 0 b) y := by
  have hDm := CERW.Support.Occupation.measurableSet_cellSet Y n
  have hDb : Bornology.IsBounded (cellSet Y n) := Metric.isBounded_ball.subset
    (CERW.Support.Occupation.cellSet_subset_ball (by norm_num) Y n)
  have hball := ball_innerRadius_subset (d := 2) (by norm_num) Y n
  rw [hb] at hball
  rw [potential_split le_rfl ε hDm hDb hb0 hball y, max_eq_right (by linarith), mul_zero,
    zero_add]

/-- Step 1 of `sec:outer-planar` and `eq:planar-exterior-pointwise`: beyond the inner radius the
bracket
is `O(r)`, so `|ℓ_n(x) - U_{D_n}(x)| ≤ K √(r lg)` for `b ≤ |x| ≤ 3n`. -/
lemma pl_first {ε : ℝ} (hε : 0 < ε) (C₀ C₁ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Y : ℕ → Site 2) (n : ℕ) (b r lg σ θ Ci : ℝ),
      LocalPathFacts 2 ε C₀ C₁ Y n → 0 < r → 0 ≤ Ci → 0 ≤ σ → σ ≤ 1 → σ * lg ≤ θ →
      2 * Ci * (4 * ε + 1) * θ ≤ 1 → 16 ≤ (n : ℝ) → r ≤ n / 8 → 4 ≤ r →
      maxRadius Y n ≤ 3 * r / 2 → Real.log n = lg → lg ≤ Real.sqrt (r * lg) →
      Real.sqrt (r * lg) = r * σ ^ 2 → |b - r| ≤ Ci * Real.sqrt (r * lg) →
      (∀ z ∈ departureRange Y n,
        (localTime Y n z : ℝ) ≤ 4 * ε * max (r - euclidNorm z) 0 + Ci * r * σ) →
      ∀ x : Site 2, b ≤ euclidNorm x → euclidNorm x ≤ 3 * n →
        |(localTime Y n x : ℝ) - potential 2 ε (cellSet Y n) (toSpace x)| ≤
          K * Real.sqrt (r * lg) := by
  obtain ⟨KS, hKS, hbra⟩ := pl_braSum_le_of_cone hε
  refine ⟨|C₁| * (Real.sqrt (2 * (KS * (16 * ε + 1))) + 2), by positivity, ?_⟩
  intro Y n b r lg σ θ Ci hP hr0 hCi0 hσ0 hσ1 hσlg hθC hn16 hrn hr4 hR hlg hlgP hPeq hbr hloc
    x hbx hx3
  obtain ⟨hL, hlog4⟩ := pl_logs hn16
  rw [hlg] at hL hlog4
  have hlg0 : 0 ≤ lg := by
    rw [← hlg]
    exact Real.log_nonneg (by linarith)
  have hR0 : 0 ≤ maxRadius Y n :=
    (euclidNorm_nonneg (Y 0)).trans (euclidNorm_le_maxRadius Y (Nat.zero_le n))
  have hP0 : 0 ≤ Real.sqrt (r * lg) := Real.sqrt_nonneg _
  have hPlg : Real.sqrt (r * lg) * lg ≤ r * θ := by
    rw [hPeq]
    calc r * σ ^ 2 * lg = r * σ * (σ * lg) := by ring
      _ ≤ r * 1 * θ := by gcongr
      _ = r * θ := by ring
  have hrσlg : r * σ * lg ≤ r * θ := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hσlg hr0.le
  have hW : braSum Y n x ≤ KS * (16 * ε + 1) * r := by
    refine (hbra Y n r b (maxRadius Y n) (Ci * r * σ) (Ci * Real.sqrt (r * lg)) (by positivity)
      (by positivity) hR0 (by linarith) (by linarith)
      (CERW.Support.Occupation.departureRange_subset_ballFinset Y n) hloc hbr x hbx hx3).trans ?_
    calc KS * (4 * ε * (2 * maxRadius Y n + 1) +
          (4 * ε * (Ci * Real.sqrt (r * lg)) + Ci * r * σ) * Real.log (4 * n + 2))
        ≤ KS * (4 * ε * (4 * r) +
          (4 * ε * (Ci * Real.sqrt (r * lg)) + Ci * r * σ) * (2 * lg)) := by
          gcongr
          linarith
      _ = KS * (16 * ε * r +
          2 * Ci * (4 * ε * (Real.sqrt (r * lg) * lg) + r * σ * lg)) := by ring
      _ ≤ KS * (16 * ε * r + 2 * Ci * (4 * ε * (r * θ) + r * θ)) := by gcongr
      _ = KS * (16 * ε * r + r * (2 * Ci * (4 * ε + 1) * θ)) := by ring
      _ ≤ KS * (16 * ε * r + r * 1) := by gcongr
      _ = KS * (16 * ε + 1) * r := by ring
  refine (hP.point x hx3).trans ?_
  exact pl_err_le (by positivity) hW (Real.log_nonneg (by linarith)) hL hlgP hr0.le

end

end CERW.Support.Outer.Radius
