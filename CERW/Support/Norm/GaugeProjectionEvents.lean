import CERW.Support.Norm.GaugeCoarseVolume
import CERW.Support.Norm.GaugeContactShape

/-!
# The compensated-path and projection-direction events for the gauge of a convex body

For the centrally excited random walk with drift opposite to subgradients of the literal Minkowski
functional `ψ = gauge K` of a convex set `K ⊆ ℝ^d` (not necessarily symmetric), under the
ellipticity condition `ε max {ψ(e_i), ψ(-e_i)} < 1/d`, this module proves the two probabilistic
estimates that the deterministic rates theorem `GaugeContactShape.Rates.ShapeRatesOfEvents` takes as
hypotheses:

* the compensated-path bound `|Z_t - Z_s| ≤ C √((t - s) log n)` for `0 ≤ s < t ≤ n`;
* the half-space martingale bounds, simultaneously for the finite deterministic family
  `projectionDirections K P n` of directions `Λ_ψ (z - P z)/|z - P z|`, `|z| ≤ n`, of a map `P`
  that is fixed before the walk (a nearest-point map onto `{ψ ≤ r_n}` for the deterministic radius
  `r_n`), and all levels `k Λ_ψ`, `k ≤ n`.

The family has at most `(2n + 1)^d` vectors, each of length at most `Λ_ψ = normMax ψ`, so that the
failure probability is at most `C n^{-p}` for every `p > 0`, with constants independent of `P`.
No coarse bound, local time bound or evenness of `ψ` enters.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.GaugeProjectionEvents

open CERW CERW.Support.Norm.MinkowskiGauge CERW.Support.Norm.GaugeModel
  CERW.Support.Norm.GaugeCoarseVolume CERW.Support.Norm.GaugeContactShape
open CERW.Support.Norm.GaugeContactShape.Projection (projDir)

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-! ## The finite deterministic family of directions -/

/-- The finite deterministic family `{Λ_ψ (z - P z)/|z - P z| : |z| ≤ n}` of the directions of the
half-space martingales, for a map `P` fixed before the walk. -/
noncomputable def projectionDirections (K : Set (EuclideanSpace ℝ (Fin d)))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    Finset (EuclideanSpace ℝ (Fin d)) :=
  (LatticeProb.ballFinset d (n : ℝ)).image fun z => projDir K P (toSpace z)

/-- Every outer-normal direction has length at most `Λ_ψ`; it is `0` at the points of the range
of `P`. -/
theorem norm_projDir_le (hΛ : 0 ≤ normMax (gauge K))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (z : EuclideanSpace ℝ (Fin d)) :
    ‖projDir K P z‖ ≤ normMax (gauge K) := by
  unfold projDir
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hΛ, abs_inv,
    abs_of_nonneg (norm_nonneg _)]
  rcases eq_or_ne ‖z - P z‖ 0 with h0 | h0
  · rw [h0]
    simpa using hΛ
  · rw [inv_mul_cancel₀ h0, mul_one]

/-- At a point off the range of `P`, the outer-normal direction has length exactly `Λ_ψ`. -/
theorem norm_projDir_of_ne (hΛ : 0 ≤ normMax (gauge K))
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {z : EuclideanSpace ℝ (Fin d)}
    (hz : z ≠ P z) : ‖projDir K P z‖ = normMax (gauge K) := by
  have hw : 0 < ‖z - P z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  rw [projDir, norm_smul, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw.ne', mul_one,
    Real.norm_of_nonneg hΛ]

/-- If `P` maps into `{ψ ≤ r}`, the outer-normal direction at a point with `ψ > r` has length
exactly `Λ_ψ`. -/
theorem norm_projDir_of_lt (hΛ : 0 ≤ normMax (gauge K))
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {r : ℝ}
    (hP : ∀ z, gauge K (P z) ≤ r) {z : EuclideanSpace ℝ (Fin d)} (hz : r < gauge K z) :
    ‖projDir K P z‖ = normMax (gauge K) := by
  refine norm_projDir_of_ne hΛ fun h => ?_
  have := hP z
  rw [← h] at this
  linarith

/-- Every vector of the family has length at most `Λ_ψ`. -/
theorem norm_le_of_mem_projectionDirections (hΛ : 0 ≤ normMax (gauge K))
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {n : ℕ}
    {q : EuclideanSpace ℝ (Fin d)} (hq : q ∈ projectionDirections K P n) :
    ‖q‖ ≤ normMax (gauge K) := by
  obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hq
  exact norm_projDir_le hΛ P _

/-- The direction at a site of Euclidean norm at most `n` belongs to the family. -/
theorem projDir_mem_projectionDirections
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {n : ℕ} {z : Site d}
    (hz : euclidNorm z ≤ n) : projDir K P (toSpace z) ∈ projectionDirections K P n :=
  Finset.mem_image_of_mem _ (LatticeProb.mem_ballFinset_iff.mpr hz)

/-- The family has at most `(2n + 1)^d` vectors. -/
theorem card_projectionDirections_le
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    ((projectionDirections K P n).card : ℝ) ≤ (2 * (n : ℝ) + 1) ^ d :=
  (Nat.cast_le.mpr Finset.card_image_le).trans
    (LatticeProb.card_ballFinset_le d (Nat.cast_nonneg n))

/-! ## The event -/

/-- The path event of the projection: start at the origin, unit steps, the compensated-path bound
with constant `C₁`, and the half-space martingale bounds with constant `C₁` for every direction of
`projectionDirections K P n` and every level `kΛ_ψ`, `k ≤ n`. -/
def ProjectionEvent (K : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C₁ : ℝ)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (n : ℕ) (x : ℕ → Site d) : Prop :=
  x 0 = 0 ∧ (∀ j, x (j + 1) - x j ∈ unitSteps d) ∧
  (∀ s t : ℕ, s < t → t ≤ n →
    ‖VectorBound.driftCompensated ε ξ x t - VectorBound.driftCompensated ε ξ x s‖ ≤
      C₁ * Real.sqrt (((t : ℝ) - s) * Real.log n)) ∧
  (∀ q ∈ projectionDirections K P n, ∀ k : ℕ, k ≤ n →
    |dynkinMart (driftStepProb d ε ξ)
        (fun z => max (inner ℝ q (toSpace z) - k * normMax (gauge K)) 0) x n| ≤
      C₁ * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
          (fun z => (k : ℝ) * normMax (gauge K) - normMax (gauge K) < inner ℝ q (toSpace z)),
        (localTime x n z : ℝ)) + Real.log n))

/-- The compensated-path hypothesis of the rates theorem, from the event. -/
theorem ProjectionEvent.compensated {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)} {C₁ : ℝ}
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {n : ℕ} {x : ℕ → Site d}
    (h : ProjectionEvent K ε ξ C₁ P n x) :
    ∀ s t : ℕ, s < t → t ≤ n →
      ‖(toSpace (x t) + ε • ∑ j ∈ Finset.range t,
          if x j ∉ departureRange x j then ξ (x j) else 0) -
        (toSpace (x s) + ε • ∑ j ∈ Finset.range s,
          if x j ∉ departureRange x j then ξ (x j) else 0)‖ ≤
        C₁ * Real.sqrt ((t - s : ℝ) * Real.log n) :=
  h.2.2.1

/-- The linear martingale hypothesis of the rates theorem, from the event: at each visited site
`x_j`, `j ≤ n`, the direction `Λ_ψ (x_j - P x_j)/|x_j - P x_j|` is in the family. -/
theorem ProjectionEvent.martingale {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)} {C₁ : ℝ}
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {n : ℕ} {x : ℕ → Site d}
    (h : ProjectionEvent K ε ξ C₁ P n x) {j : ℕ} (hj : j ≤ n) {k : ℕ} (hk : k ≤ n) :
    |dynkinMart (driftStepProb d ε ξ)
        (fun z => max (inner ℝ (projDir K P (toSpace (x j))) (toSpace z) -
          k * normMax (gauge K)) 0) x n| ≤
      C₁ * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
          (fun z => k * normMax (gauge K) - normMax (gauge K) <
            inner ℝ (projDir K P (toSpace (x j))) (toSpace z)),
        (localTime x n z : ℝ)) + Real.log n) := by
  obtain ⟨hx0, hstep, -, hmart⟩ := h
  have hxj : euclidNorm (x j) ≤ n :=
    (CERW.Support.Occupation.euclidNorm_le_of_steps x hx0 hstep j).trans (by exact_mod_cast hj)
  exact hmart _ (projDir_mem_projectionDirections hxj) k hk

/-! ## The failure probability -/

/-- A set covered by two events of small probability and a null event has small probability. -/
private lemma measure_le_of_subset_union_three {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S E₁ E₂ N : Set Ω} {a₁ a₂ C : ℝ} (hS : S ⊆ E₁ ∪ E₂ ∪ N)
    (h₁ : μ E₁ ≤ ENNReal.ofReal a₁) (h₂ : μ E₂ ≤ ENNReal.ofReal a₂) (hN : μ N = 0)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hC : a₁ + a₂ ≤ C) : μ S ≤ ENNReal.ofReal C :=
  calc μ S ≤ μ (E₁ ∪ E₂ ∪ N) := measure_mono hS
    _ ≤ μ (E₁ ∪ E₂) + μ N := measure_union_le _ _
    _ = μ (E₁ ∪ E₂) := by rw [hN, add_zero]
    _ ≤ μ E₁ + μ E₂ := measure_union_le _ _
    _ ≤ ENNReal.ofReal a₁ + ENNReal.ofReal a₂ := add_le_add h₁ h₂
    _ = ENNReal.ofReal (a₁ + a₂) := (ENNReal.ofReal_add ha₁ ha₂).symm
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hC

/-- The count of the directions in the union bound: at most `(2n+1)^d` directions and `n + 1`
levels cost at most `2 · 3^d n^{d+1}`, which `n^{-(p+d+1)}` turns into `n^{-p}`. -/
private lemma union_count_arith {C p : ℝ} (hC : 0 ≤ C) (d : ℕ) {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc : c ≤ (2 * (n : ℝ) + 1) ^ d) :
    C * (c * ((n : ℝ) + 1)) * (n : ℝ) ^ (-(p + d + 1)) ≤ (C * 2 * 3 ^ d) * (n : ℝ) ^ (-p) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hrp : 0 ≤ (n : ℝ) ^ (-(p + d + 1)) := Real.rpow_nonneg hnpos.le _
  have h1 : (2 * (n : ℝ) + 1) ^ d ≤ (3 * n) ^ d :=
    pow_le_pow_left₀ (by positivity) (by linarith) d
  have h2 : c * ((n : ℝ) + 1) ≤ 3 ^ d * (n : ℝ) ^ d * (2 * n) := by
    calc c * ((n : ℝ) + 1) ≤ (3 * (n : ℝ)) ^ d * (2 * n) :=
          mul_le_mul (hc.trans h1) (by linarith) (by positivity) (by positivity)
      _ = 3 ^ d * (n : ℝ) ^ d * (2 * n) := by rw [mul_pow]
  have h3 : (n : ℝ) ^ (-(p + d + 1)) = (n : ℝ) ^ (-p) * ((n : ℝ) ^ (d + 1))⁻¹ := by
    rw [show -(p + d + 1) = -p + -((d + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add hnpos, Real.rpow_neg hnpos.le ((d + 1 : ℕ) : ℝ), Real.rpow_natCast]
  have h4 : (n : ℝ) ^ d * n * ((n : ℝ) ^ (d + 1))⁻¹ = 1 := by
    rw [← pow_succ]
    exact mul_inv_cancel₀ (pow_ne_zero _ hnpos.ne')
  calc C * (c * ((n : ℝ) + 1)) * (n : ℝ) ^ (-(p + d + 1))
      ≤ C * (3 ^ d * (n : ℝ) ^ d * (2 * n)) * (n : ℝ) ^ (-(p + d + 1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hC) hrp
    _ = (C * 2 * 3 ^ d) * (n : ℝ) ^ (-p) * ((n : ℝ) ^ d * n * ((n : ℝ) ^ (d + 1))⁻¹) := by
        rw [h3]
        ring
    _ = (C * 2 * 3 ^ d) * (n : ℝ) ^ (-p) := by rw [h4, mul_one]

/-- **The failure probability of the projection event.** For every `p > 0` there are constants
`C₁` and `C`, chosen from the drift strength and the dimension, such that for every field `ξ` of
subgradients of the gauge, every probability space carrying the walk, every `n ≥ 2` and every map
`P` (fixed before the walk), the set of sample points whose path is not in `ProjectionEvent` has
probability at most `C n^{-p}`. The constants do not depend on `P`, and no coarse or local time
estimate is used. -/
theorem exists_projectionEvent_failure_bound (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {p : ℝ} (hp : 0 < p) :
    ∃ C₁ C : ℝ, 0 < C₁ ∧ 0 < C ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        ∀ P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        μ {ω | ¬ ProjectionEvent K ε ξ C₁ P n (fun j => X j ω)} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  have hd1 : 1 ≤ d := by omega
  have hΛ : 0 ≤ normMax (gauge K) := normMax_gauge_nonneg K
  obtain ⟨C_V, hC_V, hvec⟩ := VectorBound.exists_driftCompensated_bound.{u} hd1 hε.le hp
  obtain ⟨C_M, hC_M, hmart⟩ := exists_gauge_linear_martingale_bound hd hε hell
    (p := p + d + 1) (by positivity)
  refine ⟨max C_V C_M, C_V + C_M * 2 * 3 ^ d, lt_max_of_lt_left hC_V, by positivity, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn P
  have hξ' := drift_coord_bound_gauge hε.le hell hξ hξ0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hQ : ∀ q ∈ projectionDirections K P n, ‖q‖ ≤ normMax (gauge K) :=
    fun q hq => norm_le_of_mem_projectionDirections hΛ hq
  have h₁ := hvec hξ' hξ0 hX n hn
  have h₂ := hmart hξ hξ0 hX n hn (projectionDirections K P n) hQ
  have h₂' := h₂.trans (ENNReal.ofReal_le_ofReal
    (union_count_arith (p := p) hC_M.le d (by omega) (card_projectionDirections_le P n)))
  have hnull : μ {ω | ¬ (X 0 ω = 0 ∧ ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d)} = 0 := by
    have hpath : ∀ᵐ ω ∂μ, X 0 ω = 0 ∧ ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d := by
      have h0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
        rw [ae_iff]
        exact hX.start
      filter_upwards [h0, ae_all_iff.mpr
        (CERW.Support.Drift.ae_sub_mem_unitSteps_drift hd1 hε.le hξ' hX)] with ω h0 hs
      exact ⟨h0, hs⟩
    exact ae_iff.mp hpath
  refine measure_le_of_subset_union_three ?_ h₁ h₂' hnull (by positivity) (by positivity) ?_
  · intro ω hω
    by_contra hnot
    rw [Set.mem_union, Set.mem_union, not_or, not_or] at hnot
    obtain ⟨⟨hv, hh⟩, hpa⟩ := hnot
    have hP : X 0 ω = 0 ∧ ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d := by
      by_contra hc
      exact hpa hc
    refine hω ⟨hP.1, hP.2, ?_, ?_⟩
    · intro s t hst htn
      have h3 : ‖VectorBound.driftCompensated ε ξ (fun j => X j ω) t -
          VectorBound.driftCompensated ε ξ (fun j => X j ω) s‖ ≤
          C_V * Real.sqrt (((t : ℝ) - s) * Real.log n) := by
        by_contra hcon
        exact hv ⟨s, t, hst, htn, not_le.mp hcon⟩
      exact h3.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
    · intro q hq k hk
      have h3 : |dynkinMart (driftStepProb d ε ξ)
          (fun z => max (inner ℝ q (toSpace z) - k * normMax (gauge K)) 0)
          (fun j => X j ω) n| ≤
          C_M * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange (fun j => X j ω) n).filter
              (fun z => (k : ℝ) * normMax (gauge K) - normMax (gauge K) < inner ℝ q (toSpace z)),
            (localTime (fun j => X j ω) n z : ℝ)) + Real.log n) := by
        by_contra hcon
        exact hh ⟨q, hq, k, hk, not_le.mp hcon⟩
      refine h3.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) ?_)
      exact add_nonneg (Real.sqrt_nonneg _) hlog
  · have : C_V * (n : ℝ) ^ (-p) + C_M * 2 * 3 ^ d * (n : ℝ) ^ (-p) =
        (C_V + C_M * 2 * 3 ^ d) * (n : ℝ) ^ (-p) := by ring
    exact this.le

/-! ## The deterministic radius and the nearest-point map -/

/-- **The nearest-point map is unique.** Two maps into `{ψ ≤ r}` with the variational inequality
`(z - P z) · (y - P z) ≤ 0` for every `y` with `ψ(y) ≤ r` are equal: adding the inequalities at
`y = P' z` and at `y = P z` gives `|P' z - P z|² ≤ 0`. -/
theorem nearestPoint_unique {r : ℝ}
    {P P' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (h1 : ∀ z, gauge K (P z) ≤ r)
    (h2 : ∀ z y, gauge K y ≤ r → inner ℝ (z - P z) (y - P z) ≤ 0)
    (h1' : ∀ z, gauge K (P' z) ≤ r)
    (h2' : ∀ z y, gauge K y ≤ r → inner ℝ (z - P' z) (y - P' z) ≤ 0) : P = P' := by
  funext z
  have ha := h2 z (P' z) (h1' z)
  have hb := h2' z (P z) (h1 z)
  have hsum : inner ℝ (z - P z) (P' z - P z) + inner ℝ (z - P' z) (P z - P' z) =
      ‖P' z - P z‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm (P z) (P' z)]
    ring
  have hsq : ‖P' z - P z‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
  have hnorm : ‖P' z - P z‖ = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
  exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm

/-- **The nearest-point map onto the projected ball at the deterministic radius `r_n`.** For
`n ≥ 1`, the radius `r_n = ((d+1) n/(2 d ε |B_ψ|))^{1/(d+1)}` is positive and satisfies
`n = 2 ε d |B_ψ| r_n^{d+1}/(d+1)`, and there is exactly one map `P` with values in `{ψ ≤ r_n}` and
the variational inequality `(z - P z) · (y - P z) ≤ 0` for every `y` with `ψ(y) ≤ r_n`, that is,
the Euclidean nearest-point map onto the closed convex set `{ψ ≤ r_n}`. Existence is that of the
nearest point of a closed convex set (`Projection.exists_nearestPoint`); uniqueness is
`nearestPoint_unique`. The event `ProjectionEvent` is therefore the same for every choice. -/
theorem existsUnique_nearestPoint_at_scale (hd : 2 ≤ d) (hΨ : Adm K) {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} (hn : 1 ≤ n) :
    0 < coarseScale (gauge K) ε n ∧
      (n : ℝ) = 2 * ε * d * normBallVolume (gauge K) * coarseScale (gauge K) ε n ^ (d + 1) /
        (d + 1) ∧
      ∃! P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        (∀ z, gauge K (P z) ≤ coarseScale (gauge K) ε n) ∧
          ∀ z y, gauge K y ≤ coarseScale (gauge K) ε n → inner ℝ (z - P z) (y - P z) ≤ 0 := by
  have hd1 : 1 ≤ d := by omega
  have hV : 0 < normBallVolume (gauge K) :=
    normBallVolume_gauge_pos hΨ.compact hΨ.convex hΨ.zero_mem
  have hr := coarseScale_pos hd1 hε hV hn
  refine ⟨hr, ?_, ?_⟩
  · have h := nat_eq_coarseScale_pow (Ψ := gauge K) hd1 hε hV n
    rw [h]
    ring
  · obtain ⟨P, hP1, hP2⟩ := Projection.exists_nearestPoint hΨ hr
    exact ⟨P, ⟨hP1, hP2⟩, fun P' ⟨h1', h2'⟩ => nearestPoint_unique h1' h2' hP1 hP2⟩

end CERW.Support.Norm.GaugeProjectionEvents
