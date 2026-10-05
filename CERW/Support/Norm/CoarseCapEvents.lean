import CERW.Support.Norm.CoarseCrossing
import CERW.Support.Norm.ShapeRates
import CERW.Support.Norm.OuterCrossing

/-!
# The path event of the Euclidean cap argument and its failure probability

For a norm `Ψ`, a drift strength `ε` and a field `ξ` of subgradients, `CapEvent` is the following
explicit property of a path `x`: it starts at the origin, all its steps are unit steps, its drift
compensated position satisfies the vector bound `|Z_t - Z_s| ≤ C_V √((t - s) log n)` for all
`0 ≤ s < t ≤ n`, and the Dynkin martingales of the half-space functions `(q · x - kΛ_Ψ)_+`
satisfy the bracket bound with constant `C_M`, simultaneously for all `k ≤ n` and all directions `q`
of the finite family `capDirections Ψ n`.

* `exists_capEvent_failure_bound` bounds the probability that the walk's path is *not* in this set
  by `C n^{-p}`, with the three constants chosen before the field `ξ`, the sample space and `n`.
  It is assembled from the vector bound `VectorBound.exists_driftCompensated_bound`, the
  finite-family martingale theorem `exists_linear_martingale_bound`, the cardinality bound of the
  family and the almost sure unit steps of the walk. Only the failure set of `CapEvent` is
  bounded; nothing is asserted about any other named event.
* `exists_rough_outer_of_capEvent` applies `rough_outer_bound`, with the crossing lemma supplied by
  its proof `outer_crossing_holds`, to every path of `CapEvent`: one bound for every real `a ≥ 0`.
* `exists_rough_outer_failure_bound` is the failure probability of the rough outer bound for all
  real levels simultaneously, including levels that depend on the path.
* `exists_cap_local_failure_bound` adds the three clauses of the local time potential lemma,
  supplied by a hypothesis `norm_local_time_potential`.

No radial test, coarse bound, Moreau envelope or contact estimate is used.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.CoarseCapEvents

open CERW CERW.Support.Norm.CoarseCrossing

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ## The event -/

/-- The path event of the Euclidean cap argument: start at the origin, unit steps, the vector bound
with constant `C_V`, and the half-space martingale bounds with constant `C_M` for every direction
of `capDirections Ψ n` and every level `kΛ_Ψ`, `k ≤ n`. -/
def CapEvent (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C_V C_M : ℝ) (n : ℕ) (x : ℕ → Site d) : Prop :=
  x 0 = 0 ∧ (∀ j, x (j + 1) - x j ∈ unitSteps d) ∧
  (∀ s t : ℕ, s < t → t ≤ n →
    ‖VectorBound.driftCompensated ε ξ x t - VectorBound.driftCompensated ε ξ x s‖ ≤
      C_V * Real.sqrt (((t : ℝ) - s) * Real.log n)) ∧
  (∀ q ∈ capDirections Ψ n, ∀ k : ℕ, k ≤ n →
    |dynkinMart (driftStepProb d ε ξ)
        (fun z => max (inner ℝ q (toSpace z) - k * normMax Ψ) 0) x n| ≤
      C_M * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
          (fun z => (k : ℝ) * normMax Ψ - normMax Ψ < inner ℝ q (toSpace z)),
        (localTime x n z : ℝ)) + Real.log n))

/-- The rough outer bound for every real level `a ≥ 0`, as a property of a path. -/
def RoughOuter (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (C : ℝ) (n : ℕ) (x : ℕ → Site d) : Prop :=
  ∀ a : ℝ, 0 ≤ a →
    maxRadius x n ≤ a / normMin Ψ + C * (1 + ((((departureRange x n).filter
      (fun z => a ≤ Ψ (toSpace z))).sup (localTime x n) : ℕ) : ℝ)) * Real.log n

/-- Every path of `CapEvent` satisfies the rough outer bound for every real level, with a constant
chosen before the field, the time and the path. -/
theorem exists_rough_outer_of_capEvent (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {C_V C_M : ℝ} (hC_V : 0 < C_V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (n : ℕ), 2 ≤ n → ∀ x : ℕ → Site d,
        CapEvent Ψ ε ξ C_V C_M n x → RoughOuter Ψ C n x := by
  obtain ⟨C, hC, hmain⟩ := rough_outer_bound hd hΨ hε hell outer_crossing_holds
    (C_V := C_V) (C_M := C_M) hC_V
  refine ⟨C, hC, fun ξ hξ hξ0 n hn x hx => ?_⟩
  obtain ⟨hx0, hstep, hvec, hmart⟩ := hx
  exact fun a ha => hmain ξ hξ hξ0 n hn x hx0 hstep hvec hmart a ha


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

/-- **The failure probability of the cap event.** For every `p > 0` there are constants `C_V`,
`C_M` and `C`, chosen from the norm and the drift strength, such that for every field `ξ` of
subgradients, every probability space carrying the walk and every `n ≥ 2`, the set of sample points
whose path is not in `CapEvent` has probability at most `C n^{-p}`. The bound is on that failure set
only. -/
theorem exists_capEvent_failure_bound (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    ∃ C_V C_M C : ℝ, 0 < C_V ∧ 0 < C ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ CapEvent Ψ ε ξ C_V C_M n (fun j => X j ω)} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hc0, -⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  have hΛ : 0 ≤ normMax Ψ :=
    le_trans hc0.le (CERW.Support.Norm.ContactAssembly.normMin_le_normMax hd1 hΨ)
  obtain ⟨C_V, hC_V, hvec⟩ := VectorBound.exists_driftCompensated_bound.{u} hd1 hε.le hp
  obtain ⟨C_M, hC_M, hmart⟩ := exists_linear_martingale_bound.{u} hd hΨ hε hell
    (p := p + d + 1) (by positivity)
  refine ⟨C_V, C_M, C_V + C_M * 2 * 3 ^ d, hC_V, by positivity, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  have hξ' := CERW.Support.Norm.ContactAssembly.drift_coord_le hΨ hε hell hξ hξ0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg hnpos.le _
  have hQ : ∀ q ∈ capDirections Ψ n, ‖q‖ ≤ normMax Ψ :=
    fun q hq => norm_le_of_mem_capDirections hΛ hq
  have h₁ := hvec hξ' hξ0 hX n hn
  have h₂ := hmart hξ hξ0 hX n hn (capDirections Ψ n) hQ
  have h₂' := h₂.trans (ENNReal.ofReal_le_ofReal
    (union_count_arith (p := p) hC_M.le d (by omega) (card_capDirections_le Ψ n)))
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
      by_contra hcon
      exact hv ⟨s, t, hst, htn, not_le.mp hcon⟩
    · intro q hq k hk
      by_contra hcon
      exact hh ⟨q, hq, k, hk, not_le.mp hcon⟩
  · have : C_V * (n : ℝ) ^ (-p) + C_M * 2 * 3 ^ d * (n : ℝ) ^ (-p) =
        (C_V + C_M * 2 * 3 ^ d) * (n : ℝ) ^ (-p) := by ring
    exact this.le


/-- **The rough outer bound for all real levels, with high probability.** For every `p > 0` there
are constants `C_out` and `C` such that, for every field `ξ` of subgradients, every probability
space carrying the walk and every `n ≥ 2`, the set of sample points whose path fails the rough
outer bound `RoughOuter Ψ C_out n` at some real level `a ≥ 0` has probability at most `C n^{-p}`.
The bound is on that failure set only. -/
theorem exists_rough_outer_failure_bound (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    ∃ C_out C : ℝ, 0 < C_out ∧ 0 < C ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ RoughOuter Ψ C_out n (fun j => X j ω)} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨C_V, C_M, C, hC_V, hC, hev⟩ := exists_capEvent_failure_bound.{u} hd hΨ hε hell hp
  obtain ⟨C_out, hC_out, hcap⟩ := exists_rough_outer_of_capEvent hd hΨ hε hell
    (C_V := C_V) (C_M := C_M) hC_V
  refine ⟨C_out, C, hC_out, hC, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  refine le_trans (measure_mono ?_) (hev ξ hξ hξ0 μ X hX n hn)
  intro ω hω hcapω
  exact hω (hcap ξ hξ hξ0 n hn _ hcapω)

/-- The rough outer bound at a real level that depends on the sample point: for every function `a`
of the sample point with values in `[0, ∞)`, with the constants of
`exists_rough_outer_failure_bound`, the set of sample points at which the bound at the level
`a ω` fails has probability at most `C n^{-p}`. No measurability or regularity of `a` is used. -/
theorem exists_rough_outer_failure_bound_at_level (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ}
    (hε : 0 < ε) (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    ∃ C_out C : ℝ, 0 < C_out ∧ 0 < C ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        ∀ a : Ω → ℝ, (∀ ω, 0 ≤ a ω) →
        μ {ω | ¬ (maxRadius (fun j => X j ω) n ≤ a ω / normMin Ψ + C_out *
          (1 + ((((departureRange (fun j => X j ω) n).filter
            (fun z => a ω ≤ Ψ (toSpace z))).sup (localTime (fun j => X j ω) n) : ℕ) : ℝ)) *
          Real.log n)} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨C_out, C, hC_out, hC, hev⟩ := exists_rough_outer_failure_bound.{u} hd hΨ hε hell hp
  refine ⟨C_out, C, hC_out, hC, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn a ha
  refine le_trans (measure_mono ?_) (hev ξ hξ hξ0 μ X hX n hn)
  intro ω hω hroughω
  exact hω (hroughω (a ω) (ha ω))

/-- The inner radius `inf_{y ∉ D_n} Ψ(y)` is nonnegative: the level used for the second application
of the rough outer bound is an admissible level. -/
theorem normInnerRadius_nonneg (hΨ : IsNorm Ψ) (x : ℕ → Site d) (n : ℕ) :
    0 ≤ normInnerRadius Ψ x n :=
  Real.sInf_nonneg (by
    rintro _ ⟨y, -, rfl⟩
    exact (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 y)

/-- The rough outer bound at the random level `inf_{y ∉ D_n} Ψ(y)`, the level used in the proof of
the coarse bounds, fails with probability at most `C n^{-p}`, with the constants of
`exists_rough_outer_failure_bound`. -/
theorem exists_rough_outer_failure_bound_at_inner_radius (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ}
    (hε : 0 < ε) (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    ∃ C_out C : ℝ, 0 < C_out ∧ 0 < C ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ (maxRadius (fun j => X j ω) n ≤ normInnerRadius Ψ (fun j => X j ω) n /
            normMin Ψ + C_out * (1 + ((((departureRange (fun j => X j ω) n).filter
            (fun z => normInnerRadius Ψ (fun j => X j ω) n ≤ Ψ (toSpace z))).sup
              (localTime (fun j => X j ω) n) : ℕ) : ℝ)) * Real.log n)} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨C_out, C, hC_out, hC, hev⟩ :=
    exists_rough_outer_failure_bound_at_level.{u} hd hΨ hε hell hp
  refine ⟨C_out, C, hC_out, hC, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  exact hev ξ hξ hξ0 μ X hX n hn (fun ω => normInnerRadius Ψ (fun j => X j ω) n)
    (fun ω => normInnerRadius_nonneg hΨ _ n)

/-! ## The event together with the local time potential -/

/-- The three clauses of the local time potential lemma, as a property of a path: the largest local
time and the interval maxima, and the approximation of the cell local time by the potential of the
cell set on `{|y| ≤ 2n}`, with constant `C_L`. -/
def LocalTimeEvent (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ) (C_L : ℝ) (n : ℕ)
    (x : ℕ → Site d) : Prop :=
  (maxLocalTime x n : ℝ) ≤ C_L * ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / d) +
      C_L * Real.log n ^ 2 ∧
  (∀ s t : ℕ, s < t → t ≤ n →
    (intervalMax x s t : ℝ) ≤ C_L * (freshCount x s t : ℝ) ^ ((1 : ℝ) / d) +
      C_L * Real.log n ^ 2) ∧
  ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
    |cellLocalTime x n y - normPotential d ε Ψ (cellSet x n) y| ≤ C_L * Real.log n + C_L *
      (if d = 2 then Real.sqrt (maxLocalTime x n) * Real.log n
        else Real.sqrt (maxLocalTime x n * Real.log n))

/-- **The cap event together with the local time potential.** Given the local time potential lemma
as the hypothesis `hlocal` (its proof is `norm_local_time_potential_of cell_gradient_holds`, the
frozen theorem `CERW.Frozen.norm_local_time_potential`), for every `p > 0` there are constants such
that, for every field `ξ` of subgradients, every probability space carrying the walk and every
`n ≥ 2`, the set of sample points whose path is not in both `CapEvent` and `LocalTimeEvent` has
probability at most `C n^{-p}`. The bound is on that failure set only. -/
theorem exists_cap_local_failure_bound
    (hlocal : CERW.Support.Statements.norm_local_time_potential.{u}) (hd : 2 ≤ d)
    (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    ∃ C_V C_M C_L C : ℝ, 0 < C_V ∧ 0 < C_L ∧ 0 < C ∧
      ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ (CapEvent Ψ ε ξ C_V C_M n (fun j => X j ω) ∧
            LocalTimeEvent Ψ ε C_L n (fun j => X j ω))} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨C_V, C_M, C₁, hC_V, hC₁, hev⟩ := exists_capEvent_failure_bound.{u} hd hΨ hε hell hp
  obtain ⟨C_L, hC_L, hloc⟩ := hlocal hd Ψ hΨ ε hε hell p hp
  refine ⟨C_V, C_M, C_L, C₁ + C_L, hC_V, hC_L, by positivity, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  have h₁ := hev ξ hξ hξ0 μ X hX n hn
  have h₂ := hloc ξ hξ hξ0 μ X hX n hn
  have hnp : 0 ≤ (n : ℝ) ^ (-p) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  calc μ {ω | ¬ (CapEvent Ψ ε ξ C_V C_M n (fun j => X j ω) ∧
          LocalTimeEvent Ψ ε C_L n (fun j => X j ω))}
      ≤ μ ({ω | ¬ CapEvent Ψ ε ξ C_V C_M n (fun j => X j ω)} ∪
          {ω | ¬ LocalTimeEvent Ψ ε C_L n (fun j => X j ω)}) := by
        refine measure_mono fun ω hω => ?_
        by_contra hnot
        rw [Set.mem_union, not_or] at hnot
        exact hω ⟨not_not.mp hnot.1, not_not.mp hnot.2⟩
    _ ≤ μ {ω | ¬ CapEvent Ψ ε ξ C_V C_M n (fun j => X j ω)} +
          μ {ω | ¬ LocalTimeEvent Ψ ε C_L n (fun j => X j ω)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (C₁ * (n : ℝ) ^ (-p)) + ENNReal.ofReal (C_L * (n : ℝ) ^ (-p)) :=
        add_le_add h₁ h₂
    _ = ENNReal.ofReal ((C₁ + C_L) * (n : ℝ) ^ (-p)) := by
        rw [← ENNReal.ofReal_add (mul_nonneg hC₁.le hnp) (mul_nonneg hC_L.le hnp)]
        congr 1
        ring


/-! ## Measurability -/

/-- A property of paths that depends only on the positions up to time `n` defines a measurable set
of sample points when every position is a random variable: it is the preimage, under the past path,
of a subset of a countable space. -/
theorem measurableSet_of_agree {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → Site d}
    (hX : ∀ j, Measurable (X j)) {n : ℕ} {P : (ℕ → Site d) → Prop}
    (hP : ∀ x y : ℕ → Site d, (∀ j ≤ n, x j = y j) → (P x ↔ P y)) :
    MeasurableSet {ω | P (fun j => X j ω)} := by
  have hset : {ω | P (fun j => X j ω)} =
      CERW.Support.Law.pastPath X n ⁻¹' {q | P (CERW.Support.Law.extendPath q)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    exact hP _ _ fun j hj => (CERW.Support.Law.extendPath_pastPath X hj ω).symm
  rw [hset]
  exact CERW.Support.Law.measurable_pastPath hX n
    (Set.to_countable {q | P (CERW.Support.Law.extendPath q)}).measurableSet

/-- The compensated position at time `t ≤ n` depends only on the path up to time `n`. -/
private lemma driftCompensated_congr {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    {x y : ℕ → Site d} {n t : ℕ} (htn : t ≤ n) (h : ∀ j ≤ n, x j = y j) :
    VectorBound.driftCompensated ε ξ x t = VectorBound.driftCompensated ε ξ y t := by
  unfold VectorBound.driftCompensated
  have hx : x t = y t := h t htn
  have hs : ∑ j ∈ Finset.range t, (if x j ∉ departureRange x j then ξ (x j) else 0) =
      ∑ j ∈ Finset.range t, (if y j ∉ departureRange y j then ξ (y j) else 0) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjt : j < t := Finset.mem_range.mp hj
    have hjn : ∀ i ≤ j, x i = y i := fun i hi => h i (hi.trans (hjt.le.trans htn))
    have hdr : departureRange x j = departureRange y j := by
      unfold departureRange
      exact Finset.image_congr fun i hi => hjn i (Finset.mem_range.mp hi).le
    rw [hdr, hjn j le_rfl]
  rw [hx, hs]

/-- The departure range and the local times at time `n` depend only on the path up to time `n`. -/
private lemma departureRange_congr {x y : ℕ → Site d} {n : ℕ} (h : ∀ j ≤ n, x j = y j) :
    departureRange x n = departureRange y n :=
  Finset.image_congr fun i hi => h i (Finset.mem_range.mp hi).le

/-- The local time at time `n` depends only on the path up to time `n`. -/
private lemma localTime_congr {x y : ℕ → Site d} {n : ℕ} (h : ∀ j ≤ n, x j = y j) (z : Site d) :
    localTime x n z = localTime y n z := by
  unfold localTime
  congr 1
  refine Finset.filter_congr fun j hj => ?_
  rw [h j (Finset.mem_range.mp hj).le]

/-- The Dynkin martingale of the drift walk at time `n` depends only on the path up to time `n`. -/
private lemma dynkinMart_congr {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    {x y : ℕ → Site d} {n : ℕ} (f : Site d → ℝ) (h : ∀ j ≤ n, x j = y j) :
    dynkinMart (driftStepProb d ε ξ) f x n = dynkinMart (driftStepProb d ε ξ) f y n := by
  unfold dynkinMart
  rw [h n le_rfl, h 0 (Nat.zero_le n)]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := (Finset.mem_range.mp hj).le
  unfold stepMean
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [CERW.Support.Drift.driftStepProb_congr (fun i hi => h i (hi.trans hjn)) e, h j hjn]

/-- The set of sample points whose path is in `CapEvent` is measurable when every position is a
random variable. -/
theorem measurableSet_capEvent {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → Site d}
    (hX : ∀ j, Measurable (X j)) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C_V C_M : ℝ) (n : ℕ) :
    MeasurableSet {ω | CapEvent Ψ ε ξ C_V C_M n (fun j => X j ω)} := by
  have hstart : MeasurableSet {ω | X 0 ω = 0} :=
    measurableSet_eq_fun (hX 0) measurable_const
  have hsteps : MeasurableSet {ω | ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d} := by
    have : {ω | ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d} =
        ⋂ j, {ω | X (j + 1) ω - X j ω ∈ unitSteps d} := by
      ext ω
      simp
    rw [this]
    refine MeasurableSet.iInter fun j => ?_
    exact measurableSet_of_agree (n := j + 1) (P := fun x => x (j + 1) - x j ∈ unitSteps d) hX
      (fun x y h => by rw [h (j + 1) le_rfl, h j (Nat.le_succ j)])
  have hvec : MeasurableSet {ω | ∀ s t : ℕ, s < t → t ≤ n →
      ‖VectorBound.driftCompensated ε ξ (fun j => X j ω) t -
        VectorBound.driftCompensated ε ξ (fun j => X j ω) s‖ ≤
        C_V * Real.sqrt (((t : ℝ) - s) * Real.log n)} :=
    measurableSet_of_agree (n := n) hX (P := fun x => ∀ s t : ℕ, s < t → t ≤ n →
      ‖VectorBound.driftCompensated ε ξ x t - VectorBound.driftCompensated ε ξ x s‖ ≤
        C_V * Real.sqrt (((t : ℝ) - s) * Real.log n))
      (fun x y h => by
        refine forall_congr' fun s => forall_congr' fun t => forall_congr' fun hst =>
          forall_congr' fun htn => ?_
        rw [driftCompensated_congr htn h, driftCompensated_congr (hst.le.trans htn) h])
  have hhs : MeasurableSet {ω | ∀ q ∈ capDirections Ψ n, ∀ k : ℕ, k ≤ n →
      |dynkinMart (driftStepProb d ε ξ)
          (fun z => max (inner ℝ q (toSpace z) - k * normMax Ψ) 0) (fun j => X j ω) n| ≤
        C_M * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange (fun j => X j ω) n).filter
            (fun z => (k : ℝ) * normMax Ψ - normMax Ψ < inner ℝ q (toSpace z)),
          (localTime (fun j => X j ω) n z : ℝ)) + Real.log n)} :=
    measurableSet_of_agree (n := n) hX (P := fun x => ∀ q ∈ capDirections Ψ n, ∀ k : ℕ, k ≤ n →
      |dynkinMart (driftStepProb d ε ξ)
          (fun z => max (inner ℝ q (toSpace z) - k * normMax Ψ) 0) x n| ≤
        C_M * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
            (fun z => (k : ℝ) * normMax Ψ - normMax Ψ < inner ℝ q (toSpace z)),
          (localTime x n z : ℝ)) + Real.log n))
      (fun x y h => by
        refine forall_congr' fun q => forall_congr' fun hq => forall_congr' fun k =>
          forall_congr' fun hk => ?_
        rw [dynkinMart_congr _ h, departureRange_congr h]
        have hsum : ∑ z ∈ (departureRange y n).filter
            (fun z => (k : ℝ) * normMax Ψ - normMax Ψ < inner ℝ q (toSpace z)),
              (localTime x n z : ℝ) = ∑ z ∈ (departureRange y n).filter
            (fun z => (k : ℝ) * normMax Ψ - normMax Ψ < inner ℝ q (toSpace z)),
              (localTime y n z : ℝ) :=
          Finset.sum_congr rfl fun z _ => by rw [localTime_congr h z]
        rw [hsum])
  have : {ω | CapEvent Ψ ε ξ C_V C_M n (fun j => X j ω)} =
      {ω | X 0 ω = 0} ∩ {ω | ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d} ∩ {ω | ∀ s t : ℕ, s < t →
      t ≤ n → ‖VectorBound.driftCompensated ε ξ (fun j => X j ω) t -
        VectorBound.driftCompensated ε ξ (fun j => X j ω) s‖ ≤
        C_V * Real.sqrt (((t : ℝ) - s) * Real.log n)} ∩ {ω | ∀ q ∈ capDirections Ψ n,
      ∀ k : ℕ, k ≤ n →
      |dynkinMart (driftStepProb d ε ξ)
          (fun z => max (inner ℝ q (toSpace z) - k * normMax Ψ) 0) (fun j => X j ω) n| ≤
        C_M * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange (fun j => X j ω) n).filter
            (fun z => (k : ℝ) * normMax Ψ - normMax Ψ < inner ℝ q (toSpace z)),
          (localTime (fun j => X j ω) n z : ℝ)) + Real.log n)} := by
    ext ω
    simp only [CapEvent, Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
  rw [this]
  exact ((hstart.inter hsteps).inter hvec).inter hhs

end CERW.Support.Norm.CoarseCapEvents
