import CERW.Support.Norm.GaugeLaplacianSharp
import CERW.Support.Norm.GaugeResults
import CERW.Support.Norm.GaugeShapeEvents
import CERW.Support.Norm.ContactEvent
import CERW.Support.Norm.Section5Localization
import CERW.Frozen.NormShapeRates

/-!
# A norm is the Minkowski functional of its closed unit ball, and the consequences for a norm

Let `d ≥ 1` and let `Ψ` be a norm on `ℝ^d` (`IsNorm Ψ`). Its closed unit ball is
`K = {x | Ψ x ≤ 1}`. This module proves that `K` is compact and convex, that the origin is an
interior point of `K`, that the interior of `K` is the open unit ball `{Ψ < 1}`, and that the
Minkowski functional of `K` is `Ψ` itself, `gauge K = Ψ`. Consequently `Λ_Ψ = Λ_{gauge K}`,
`c_Ψ = c_{gauge K}`, the volume `|B_Ψ|` of the open unit ball is the volume `|K|` of the body, and
the subgradients of `gauge K` are the subgradients of `Ψ`.

The identification instantiates, at a norm, the results that were stated for the Minkowski
functional of a compact convex body with the origin in its interior:

* `exists_unique_isDistribLaplacian_norm_sharp`, `norm_measure_ball_le_sharp`: the distributional
  Laplacian `μ` of `Ψ` is the unique locally finite measure with `∫ φ dμ = ∫ Ψ Δφ` for every
  smooth compactly supported `φ`; it charges every ball about the origin and satisfies the
  displayed growth estimate `μ(B(y, R)) ≤ 2^(d+1) ω_d Λ_Ψ R^(d-1)` of the source with its exact
  coefficient (applying `GaugeLaplacianSharp`).
* `norm_volume_limit`: almost surely `|A_n| / r_n^d → |B_Ψ|` (applying `GaugeResults.gauge_volume_limit`).
* `norm_inner_radius_upper_bound`: with probability at least `1 - C n^{-p}`,
  `(R_in(n) - r_n)_+ ≤ C (r_n^{(3-d)/2} (log n)^{1/2} + 1)` for every `n ≥ 2`
  (applying `GaugeResults.gauge_inner_radius_upper_bound`).
* `sq_euclidNorm_eq_dynkin_norm` (applying `GaugeShapeEvents.sq_euclidNorm_eq_gauge`),
  `sq_euclidNorm_eq_norm`, `ae_sq_euclidNorm_eq_norm`: the displayed identity
  `|X_n|² = n - 2ε Σ_{x ∈ A_n} Ψ(x) + 𝒬_n` with the explicit process
  `𝒬_t = Σ_{j<t} 2 X_j · (X_{j+1} - X_j + ε I_j ξ(X_j))`, along every path from the origin with unit
  steps (hence almost surely for every centrally excited random walk);
  `quadraticMartingale_ae_eq_driftDynkin` identifies `𝒬` almost surely with the Dynkin process of
  `|·|²` for the drift kernel, and `martingale_driftDynkin_sq` states that this process is a
  martingale for the natural filtration of the walk.

The inclusion form of the rates, stated after Theorem 2.1 of the source, is proved for a norm and
for the Minkowski functional of a convex body:

* `norm_shape_rates_inclusions`, `gauge_shape_rates_inclusions`: for every `p > 0` there is a
  constant `C > 0`, depending only on `d, ε, Ψ` (resp. `d, ε, K`) and `p`, such that for every
  choice of subgradients `ξ` with `ξ 0 = 0`, every walk with drift field `ξ` and every integer
  `n ≥ 2`, with probability at least `1 - C n^{-p}` the following hold simultaneously: the local
  times differ from the cone `2dε(r_n - Ψ)₊` by at most `B_n`, where `B_n = C r_n^{5/6} (log n)^{1/6}`
  if `d = 2` and `B_n = C r_n^{d/(d+1)} (log n)^{1/(d+1)}` if `d ≥ 3`; every lattice point `x` with
  `Ψ(x) < r_n - (log n) B_n` is a departed site; and every departed site `x` has
  `Ψ(x) < r_n + (log n) B_n`. They apply the registered `CERW.Frozen.norm_shape_rates`
  (resp. `GaugeResults.gauge_rates`), which hold for every `n ≥ 2`; no finite-time extension is
  needed. The constant `C₀` of the producer is enlarged to `K = C₀ (1 + m⁻¹) + 1` by the explicit
  argument of `exists_inclusion_constant`: for `n ≥ 2` the radius `r_n` is at least `r_2` and
  `log n ≥ log 2`, so `m = r_2^{1/12} (log 2)^{11/12}` (for `d ≥ 3`,
  `m = r_2^{e₁} (log 2)^{e₂}` with `e₁ = d/(d+1) - 1/2` and `e₂ = (d+2)/(d+1) - 1/2`) satisfies
  `m · (inner bound) ≤ (outer bound) = (log n) · b_n`, where `b_n = r_n^{5/6} (log n)^{1/6}`
  (`d = 2`) or `r_n^{d/(d+1)} (log n)^{1/(d+1)}` (`d ≥ 3`). Hence the inner bound `C₀ a_in` is at
  most `(log n) K b_n`, and, since `K > C₀`, the outer bound `C₀ a_out` is strictly smaller than
  `(log n) K b_n`, which gives the strict inclusion of the departed sites.

Nothing in this module is a hypothesis standing for a result of the source: every statement
applies the proved producers named above and uses no placeholder.
-/

universe u

open MeasureTheory Filter Topology Metric Set
open scoped Pointwise
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.NormGaugeConsequences

open CERW CERW.Support.Norm.MinkowskiGauge CERW.Support.Norm.GaugeModel

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ## A norm is the Minkowski functional of its closed unit ball -/

/-- The closed unit ball `{x | Ψ x ≤ 1}` of a norm `Ψ`. -/
def normClosedUnitBall (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | Ψ x ≤ 1}

/-- The closed unit ball of a norm is compact. -/
theorem isCompact_normClosedUnitBall (hd : 1 ≤ d) (hΨ : IsNorm Ψ) :
    IsCompact (normClosedUnitBall Ψ) := by
  obtain ⟨hpos, hle⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd
  have hclosed : IsClosed (normClosedUnitBall Ψ) :=
    isClosed_le (CERW.Generic.Norm.norm_continuous hΨ) continuous_const
  refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
  refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin d)))
    (r := (normMin Ψ)⁻¹)).subset ?_
  intro x hx
  rw [mem_closedBall_zero_iff]
  have h1 : normMin Ψ * ‖x‖ ≤ 1 := (hle x).trans hx
  have h2 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hpos.le)
  rwa [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul, mul_one] at h2

/-- The closed unit ball of a norm is convex. -/
theorem convex_normClosedUnitBall (hΨ : IsNorm Ψ) : Convex ℝ (normClosedUnitBall Ψ) := by
  intro x hx y hy a b ha hb hab
  have hx' : Ψ x ≤ 1 := hx
  have hy' : Ψ y ≤ 1 := hy
  show Ψ (a • x + b • y) ≤ 1
  calc Ψ (a • x + b • y) ≤ Ψ (a • x) + Ψ (b • y) := hΨ.add_le _ _
    _ = a * Ψ x + b * Ψ y := by
        rw [hΨ.smul, hΨ.smul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * 1 + b * 1 := by gcongr
    _ = 1 := by rw [mul_one, mul_one, hab]

/-- The origin is an interior point of the closed unit ball of a norm. -/
theorem zero_mem_interior_normClosedUnitBall (hΨ : IsNorm Ψ) :
    (0 : EuclideanSpace ℝ (Fin d)) ∈ interior (normClosedUnitBall Ψ) := by
  have hopen : IsOpen {x : EuclideanSpace ℝ (Fin d) | Ψ x < 1} :=
    isOpen_lt (CERW.Generic.Norm.norm_continuous hΨ) continuous_const
  have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ {x : EuclideanSpace ℝ (Fin d) | Ψ x < 1} := by
    show Ψ 0 < 1
    rw [(CERW.Generic.Norm.map_zero_nonneg_neg hΨ).1]
    exact one_pos
  exact interior_maximal (fun x (hx : Ψ x < 1) => (le_of_lt hx : Ψ x ≤ 1)) hopen h0

/-- **A norm is the Minkowski functional of its closed unit ball**: `gauge {Ψ ≤ 1} = Ψ`. -/
theorem gauge_normClosedUnitBall (hd : 1 ≤ d) (hΨ : IsNorm Ψ) :
    gauge (normClosedUnitBall Ψ) = Ψ := by
  have hK := isCompact_normClosedUnitBall hd hΨ
  have hc := convex_normClosedUnitBall hΨ
  have h0 := zero_mem_interior_normClosedUnitBall hΨ
  obtain ⟨hz, hnn, -⟩ := CERW.Generic.Norm.map_zero_nonneg_neg hΨ
  funext x
  by_cases hx : x = 0
  · subst hx
    rw [gauge_zero, hz]
  · have hxpos : 0 < Ψ x := lt_of_le_of_ne (hnn x) (fun h => hx (hΨ.eq_zero x h.symm))
    have hgpos : 0 < gauge (normClosedUnitBall Ψ) x := gauge_pos_of_ne_zero hK h0 hx
    apply le_antisymm
    · have hmem : (Ψ x)⁻¹ • x ∈ normClosedUnitBall Ψ := by
        show Ψ ((Ψ x)⁻¹ • x) ≤ 1
        rw [hΨ.smul, abs_of_pos (inv_pos.2 hxpos), inv_mul_cancel₀ hxpos.ne']
      have h1 := (gauge_le_one_iff hK hc h0 _).2 hmem
      rw [gauge_smul_nonneg _ (inv_pos.2 hxpos).le] at h1
      rwa [← div_eq_inv_mul, div_le_one hxpos] at h1
    · have hmem : (gauge (normClosedUnitBall Ψ) x)⁻¹ • x ∈ normClosedUnitBall Ψ := by
        rw [← gauge_le_one_iff hK hc h0,
          gauge_smul_nonneg _ (inv_pos.2 hgpos).le, inv_mul_cancel₀ hgpos.ne']
      have h2 : Ψ ((gauge (normClosedUnitBall Ψ) x)⁻¹ • x) ≤ 1 := hmem
      rw [hΨ.smul, abs_of_pos (inv_pos.2 hgpos)] at h2
      rwa [← div_eq_inv_mul, div_le_one hgpos] at h2

/-- The interior of the closed unit ball of a norm is its open unit ball `B_Ψ = {Ψ < 1}`. -/
theorem interior_normClosedUnitBall (hd : 1 ≤ d) (hΨ : IsNorm Ψ) :
    interior (normClosedUnitBall Ψ) = {x | Ψ x < 1} := by
  ext x
  have h := gauge_lt_one_iff (convex_normClosedUnitBall hΨ)
    (zero_mem_interior_normClosedUnitBall hΨ) x
  rw [gauge_normClosedUnitBall hd hΨ] at h
  exact h.symm

/-- `Λ_{gauge K} = Λ_Ψ` for the closed unit ball `K` of the norm `Ψ`. -/
theorem normMax_gauge_normClosedUnitBall (hd : 1 ≤ d) (hΨ : IsNorm Ψ) :
    normMax (gauge (normClosedUnitBall Ψ)) = normMax Ψ := by
  rw [gauge_normClosedUnitBall hd hΨ]

/-- `c_{gauge K} = c_Ψ` for the closed unit ball `K` of the norm `Ψ`. -/
theorem normMin_gauge_normClosedUnitBall (hd : 1 ≤ d) (hΨ : IsNorm Ψ) :
    normMin (gauge (normClosedUnitBall Ψ)) = normMin Ψ := by
  rw [gauge_normClosedUnitBall hd hΨ]

/-- The volume `|B_Ψ|` of the open unit ball of a norm is the volume `|K|` of its closed unit ball
(the unit sphere is a null set). -/
theorem normBallVolume_eq_volume_normClosedUnitBall (hd : 1 ≤ d) (hΨ : IsNorm Ψ) :
    normBallVolume Ψ = (volume (normClosedUnitBall Ψ)).toReal := by
  have h := normBallVolume_gauge (isCompact_normClosedUnitBall hd hΨ)
    (convex_normClosedUnitBall hΨ) (zero_mem_interior_normClosedUnitBall hΨ)
  rwa [gauge_normClosedUnitBall hd hΨ] at h

/-- The unit ball of a norm has positive volume. -/
theorem normBallVolume_pos_of_isNorm (hd : 1 ≤ d) (hΨ : IsNorm Ψ) : 0 < normBallVolume Ψ := by
  have h := normBallVolume_gauge_pos (isCompact_normClosedUnitBall hd hΨ)
    (convex_normClosedUnitBall hΨ) (zero_mem_interior_normClosedUnitBall hΨ)
  rwa [gauge_normClosedUnitBall hd hΨ] at h

/-- The subgradients of `gauge K` at every point are the subgradients of `Ψ`, for the closed unit
ball `K` of the norm `Ψ`. -/
theorem isSubgradient_gauge_normClosedUnitBall_iff (hd : 1 ≤ d) (hΨ : IsNorm Ψ)
    (x ξ : EuclideanSpace ℝ (Fin d)) :
    IsSubgradient (gauge (normClosedUnitBall Ψ)) x ξ ↔ IsSubgradient Ψ x ξ := by
  rw [gauge_normClosedUnitBall hd hΨ]

/-- The ellipticity assumption `ε Ψ(e_i) < 1/d` of the norm setting gives the two-sided assumption
`ε ψ(± e_i) < 1/d` of the Minkowski functional `ψ = gauge K`, since a norm is even. -/
theorem ellipticity_gauge_normClosedUnitBall (hd : 1 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ}
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) (i : Fin d) :
    ε * gauge (normClosedUnitBall Ψ) (coordVec i) < 1 / (d : ℝ) ∧
      ε * gauge (normClosedUnitBall Ψ) (-coordVec i) < 1 / (d : ℝ) := by
  rw [gauge_normClosedUnitBall hd hΨ, (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.2]
  exact ⟨hell i, hell i⟩

/-- **A norm is exactly the Minkowski functional of its closed unit ball.** For `d ≥ 1` and a norm
`Ψ`, the closed unit ball `K = {Ψ ≤ 1}` is a compact convex set with the origin in its interior,
its interior is the open unit ball, `gauge K = Ψ`, the constants `Λ` and `c` agree, the volume of
the open unit ball is the volume of `K`, and subgradients of `gauge K` and of `Ψ` coincide. -/
theorem isNorm_eq_gauge_normClosedUnitBall (hd : 1 ≤ d) (hΨ : IsNorm Ψ) :
    IsCompact (normClosedUnitBall Ψ) ∧ Convex ℝ (normClosedUnitBall Ψ) ∧
      (0 : EuclideanSpace ℝ (Fin d)) ∈ interior (normClosedUnitBall Ψ) ∧
      interior (normClosedUnitBall Ψ) = {x | Ψ x < 1} ∧
      gauge (normClosedUnitBall Ψ) = Ψ ∧
      normMax (gauge (normClosedUnitBall Ψ)) = normMax Ψ ∧
      normMin (gauge (normClosedUnitBall Ψ)) = normMin Ψ ∧
      normBallVolume Ψ = (volume (normClosedUnitBall Ψ)).toReal ∧
      ∀ x ξ : EuclideanSpace ℝ (Fin d),
        IsSubgradient (gauge (normClosedUnitBall Ψ)) x ξ ↔ IsSubgradient Ψ x ξ :=
  ⟨isCompact_normClosedUnitBall hd hΨ, convex_normClosedUnitBall hΨ,
    zero_mem_interior_normClosedUnitBall hΨ, interior_normClosedUnitBall hd hΨ,
    gauge_normClosedUnitBall hd hΨ, normMax_gauge_normClosedUnitBall hd hΨ,
    normMin_gauge_normClosedUnitBall hd hΨ, normBallVolume_eq_volume_normClosedUnitBall hd hΨ,
    isSubgradient_gauge_normClosedUnitBall_iff hd hΨ⟩

/-! ## The exact growth of the distributional Laplacian of a norm -/

/-- **`eq:hessian-growth` for a norm, with the exact coefficient.** Let `Ψ` be a norm on `ℝ^d`,
`d ≥ 1`, and let `m` be a locally finite measure with `∫ φ dm = ∫ Ψ Δφ` for every smooth compactly
supported `φ`. Then `m(B(y, R)) ≤ 2^(d+1) ω_d Λ_Ψ R^(d-1)` for every `y` and every `R > 0`. -/
theorem norm_measure_ball_le_sharp (hd : 1 ≤ d) (hΨ : IsNorm Ψ)
    {m : Measure (EuclideanSpace ℝ (Fin d))} (hm : IsLocallyFiniteMeasure m)
    (hlap : IsDistribLaplacian Ψ m) (y : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 < R) :
    m (ball y R) ≤
      ENNReal.ofReal (2 ^ (d + 1) * unitBallVolume d * normMax Ψ * R ^ (d - 1)) := by
  have hg := gauge_normClosedUnitBall hd hΨ
  have h := CERW.Support.Norm.GaugeLaplacianSharp.measure_ball_le_gauge_sharp hd
    (isCompact_normClosedUnitBall hd hΨ) (convex_normClosedUnitBall hΨ)
    (zero_mem_interior_normClosedUnitBall hΨ) hm (by rw [hg]; exact hlap) y hR
  rwa [hg] at h

/-- **The distributional Laplacian of a norm, with its exact growth.** For a norm `Ψ` on `ℝ^d`,
`d ≥ 1`, there is exactly one locally finite measure `m` with `∫ φ dm = ∫ Ψ Δφ` for every smooth
compactly supported `φ`; it charges every ball about the origin, and
`m(B(y, R)) ≤ 2^(d+1) ω_d Λ_Ψ R^(d-1)` for every `y` and every `R > 0`. -/
theorem exists_unique_isDistribLaplacian_norm_sharp (hd : 1 ≤ d) (hΨ : IsNorm Ψ) :
    ∃ m : Measure (EuclideanSpace ℝ (Fin d)),
      (IsLocallyFiniteMeasure m ∧ IsDistribLaplacian Ψ m) ∧
      (∀ m' : Measure (EuclideanSpace ℝ (Fin d)), IsLocallyFiniteMeasure m' →
        IsDistribLaplacian Ψ m' → m' = m) ∧
      (∀ {ρ : ℝ}, 0 < ρ → 0 < m (ball 0 ρ)) ∧
      ∀ (y : EuclideanSpace ℝ (Fin d)) {R : ℝ}, 0 < R →
        m (ball y R) ≤
          ENNReal.ofReal (2 ^ (d + 1) * unitBallVolume d * normMax Ψ * R ^ (d - 1)) := by
  have h := CERW.Support.Norm.GaugeLaplacianSharp.exists_unique_isDistribLaplacian_gauge_sharp hd
    (isCompact_normClosedUnitBall hd hΨ) (convex_normClosedUnitBall hΨ)
    (zero_mem_interior_normClosedUnitBall hΨ)
  rwa [gauge_normClosedUnitBall hd hΨ] at h

/-- **The exact growth at the lattice sites, for a norm.** There is a locally finite measure `m`
with distributional Laplacian `ΔΨ` and `m(B(y, R)) ≤ (2^(d+1) ω_d Λ_Ψ) R^(d-1)` for every site `y`
of `ℤ^d` and every `R > 0`. -/
theorem exists_isDistribLaplacian_norm_growth_sharp (hd : 1 ≤ d) (hΨ : IsNorm Ψ) :
    ∃ m : Measure (EuclideanSpace ℝ (Fin d)), IsLocallyFiniteMeasure m ∧
      IsDistribLaplacian Ψ m ∧ ∀ (y : Site d) {R : ℝ}, 0 < R →
        m (ball (toSpace y) R) ≤
          ENNReal.ofReal ((2 ^ (d + 1) * unitBallVolume d * normMax Ψ) * R ^ (d - 1)) := by
  have h := CERW.Support.Norm.GaugeLaplacianSharp.exists_isDistribLaplacian_gauge_growth_sharp hd
    (isCompact_normClosedUnitBall hd hΨ) (convex_normClosedUnitBall hΨ)
    (zero_mem_interior_normClosedUnitBall hΨ)
  rwa [gauge_normClosedUnitBall hd hΨ] at h

/-! ## The volume of the range, the one-sided inner radius bound -/

/-- **The volume limit for a norm** (`|A_n| / r_n^d → |B_Ψ|`, the consequence of part (i) of
Theorem 2.1 stated after it). Let `d ≥ 2`, `Ψ` a norm, `ξ(x) ∈ ∂Ψ(x)` at the sites `x ≠ 0` with
`ξ(0) = 0`, `ε > 0` with `ε Ψ(e_i) < 1/d`, and `X` a walk with drift field `ξ`. Then, almost
surely, `|A_n| / r_n^d → |B_Ψ|`, where `r_n = ((d+1) n/(2 d ε |B_Ψ|))^{1/(d+1)}`. -/
theorem norm_volume_limit (hd : 2 ≤ d) (hΨ : IsNorm Ψ)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    {ε : ℝ} (hε : 0 < ε) (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : IsDriftCERW μ ε ξ X) :
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => ((departureRange (X · ω) n).card : ℝ) / r n ^ d) atTop
      (𝓝 (normBallVolume Ψ)) := by
  have hd1 : 1 ≤ d := by omega
  have hg := gauge_normClosedUnitBall hd1 hΨ
  have hvol := normBallVolume_eq_volume_normClosedUnitBall hd1 hΨ
  have h := CERW.Support.Norm.GaugeResults.gauge_volume_limit hd
    (isCompact_normClosedUnitBall hd1 hΨ) (convex_normClosedUnitBall hΨ)
    (zero_mem_interior_normClosedUnitBall hΨ)
    (fun x hx => by rw [hg]; exact hξ x hx) hξ0 hε
    (ellipticity_gauge_normClosedUnitBall hd1 hΨ hell) μ X hX
  dsimp only at h ⊢
  rw [hvol]
  exact h

/-- **The one-sided bound on the inner radius, for a norm** (the bound after `eq:norm-inradius`).
Let `d ≥ 2`, `Ψ` a norm and `ε > 0` with `ε Ψ(e_i) < 1/d`. For every `p > 0` there is `C > 0`,
chosen before the subgradients, the probability space, the walk and `n`, such that for every
choice of subgradients with `ξ(0) = 0`, every walk with drift field `ξ` and every `n ≥ 2`, with
probability at least `1 - C n^{-p}`,
`(R_in(n) - r_n)_+ ≤ C (r_n^{(3-d)/2} (log n)^{1/2} + 1)`. -/
theorem norm_inner_radius_upper_bound (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))
    ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ (max (normInnerRadius Ψ (X · ω) n - r n) 0 ≤
            C * (r n ^ (((3 : ℝ) - d) / 2) * Real.log n ^ ((1 : ℝ) / 2) + 1))} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  have hd1 : 1 ≤ d := by omega
  have hg := gauge_normClosedUnitBall hd1 hΨ
  have hvol := normBallVolume_eq_volume_normClosedUnitBall hd1 hΨ
  have hV : 0 ≤ normBallVolume Ψ := (normBallVolume_pos_of_isNorm hd1 hΨ).le
  have h := CERW.Support.Norm.GaugeResults.gauge_inner_radius_upper_bound hd
    (isCompact_normClosedUnitBall hd1 hΨ) (convex_normClosedUnitBall hΨ)
    (zero_mem_interior_normClosedUnitBall hΨ) hε
    (ellipticity_gauge_normClosedUnitBall hd1 hΨ hell) hp
  dsimp only at h ⊢
  rw [← hvol, hg] at h
  obtain ⟨C, hC, hmain⟩ := h
  refine ⟨C, hC, fun ξ hξ hξ0 Ω _ μ _ X hX n hn => ?_⟩
  refine le_trans (measure_mono ?_) (hmain ξ hξ hξ0 μ X hX n hn)
  intro ω hω hcontra
  refine hω (max_le hcontra ?_)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hr : 0 ≤ ((d + 1) * (n : ℝ) / (2 * d * ε * normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1)) :=
    Real.rpow_nonneg (by positivity) _
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  exact mul_nonneg hC.le (add_nonneg (mul_nonneg (Real.rpow_nonneg hr _)
    (Real.rpow_nonneg hlog _)) zero_le_one)

/-! ## The identity `eq:quadratic` for a norm -/

/-- A unit step changes the squared norm by `2 ⟪x, e⟫ + 1`. -/
theorem euclidNorm_sq_add_unit (x e : Site d) (he : e ∈ unitSteps d) :
    euclidNorm (x + e) ^ 2 = euclidNorm x ^ 2 + 2 * inner ℝ (toSpace x) (toSpace e) + 1 := by
  have hto : toSpace (x + e) = toSpace x + toSpace e := by
    apply PiLp.ext
    intro i
    simp [toSpace_apply, Pi.add_apply, Int.cast_add]
  have he1 : euclidNorm e = 1 := CERW.Support.Law.euclidNorm_of_mem_unitSteps he
  have hnorm : ‖toSpace e‖ = 1 := by rw [norm_toSpace, he1]
  rw [← norm_toSpace (x + e), ← norm_toSpace x, hto, norm_add_sq_real, hnorm]
  ring

/-- **The exact quadratic identity for a norm, with the Dynkin martingale.** Applying the identity
proved for the Minkowski functional of a convex body (`GaugeShapeEvents.sq_euclidNorm_eq_gauge`) at
the closed unit ball of the norm `Ψ`: for a path `x` from the origin, `ξ(x) ∈ ∂Ψ(x)` for `x ≠ 0`,
`|x_n|² = n - 2ε Σ_{y ∈ A_n} Ψ(y) + 𝒬_n`, where `𝒬` is the Dynkin martingale of `|·|²` for the
drift one-step law. -/
theorem sq_euclidNorm_eq_dynkin_norm (hd : 1 ≤ d) (hΨ : IsNorm Ψ) (ε : ℝ)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) (x : ℕ → Site d)
    (h0 : x 0 = 0) (n : ℕ) :
    euclidNorm (x n) ^ 2 =
      n - 2 * ε * ∑ y ∈ departureRange x n, Ψ (toSpace y) +
        dynkinMart (driftStepProb d ε ξ) (fun z : Site d => euclidNorm z ^ 2) x n := by
  have hg := gauge_normClosedUnitBall hd hΨ
  have h := CERW.Support.Norm.GaugeShapeEvents.sq_euclidNorm_eq_gauge (K := normClosedUnitBall Ψ)
    hd ε (ξ := ξ) (fun x hx => by rw [hg]; exact hξ x hx) x h0 n
  rwa [hg] at h

/-- **`eq:quadratic` for a norm, pathwise.** Let `Ψ` be a norm, `ξ(x) ∈ ∂Ψ(x)` for `x ≠ 0` (the
value `ξ(0)` is irrelevant), and let `x` be a path from the origin with unit steps. Then, for every `n`,
`|x_n|² = n - 2ε Σ_{y ∈ A_n} Ψ(y) + 𝒬_n`, where
`𝒬_n = Σ_{j<n} 2 x_j · (x_{j+1} - x_j + ε I_j ξ(x_j))` and `I_j` is the indicator that `x_j` is not
among `x_0, …, x_{j-1}`. -/
theorem sq_euclidNorm_eq_norm (hΨ : IsNorm Ψ) (ε : ℝ)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x))
    {x : ℕ → Site d} (h0 : x 0 = 0) (hs : ∀ j, x (j + 1) - x j ∈ unitSteps d) (n : ℕ) :
    euclidNorm (x n) ^ 2 =
      n - 2 * ε * ∑ y ∈ departureRange x n, Ψ (toSpace y) +
        CERW.Support.Norm.ContactEvent.quadraticMartingale d ε ξ x n := by
  have hz : Ψ 0 = 0 := (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).1
  have hto0 : toSpace (0 : Site d) = 0 := by
    apply PiLp.ext
    intro i
    simp [toSpace_apply]
  induction n with
  | zero =>
    simp [h0, CERW.Support.Norm.ContactEvent.quadraticMartingale, departureRange, euclidNorm]
  | succ n ih =>
    have hdep : departureRange x (n + 1) = insert (x n) (departureRange x n) := by
      simp [departureRange, Finset.range_add_one, Finset.image_insert]
    have hQ : CERW.Support.Norm.ContactEvent.quadraticMartingale d ε ξ x (n + 1) =
        CERW.Support.Norm.ContactEvent.quadraticMartingale d ε ξ x n +
          2 * inner ℝ (toSpace (x n))
            (toSpace (x (n + 1)) - toSpace (x n) +
              ε • (if x n ∉ departureRange x n then ξ (x n) else 0)) := by
      simp only [CERW.Support.Norm.ContactEvent.quadraticMartingale, Finset.sum_range_succ]
    have hstep : x (n + 1) = x n + (x (n + 1) - x n) := by abel
    have hsq : euclidNorm (x (n + 1)) ^ 2 = euclidNorm (x n) ^ 2 +
        2 * inner ℝ (toSpace (x n)) (toSpace (x (n + 1)) - toSpace (x n)) + 1 := by
      have h1 := euclidNorm_sq_add_unit (x n) (x (n + 1) - x n) (hs n)
      rw [← hstep] at h1
      have hsub : toSpace (x (n + 1) - x n) = toSpace (x (n + 1)) - toSpace (x n) := by
        apply PiLp.ext
        intro i
        simp [toSpace_apply, Int.cast_sub]
      rw [hsub] at h1
      exact h1
    have hI : inner ℝ (toSpace (x n))
        (ε • (if x n ∉ departureRange x n then ξ (x n) else 0)) =
        if x n ∉ departureRange x n then ε * Ψ (toSpace (x n)) else 0 := by
      by_cases hmem : x n ∈ departureRange x n
      · simp [hmem]
      · by_cases hx0 : x n = 0
        · rw [if_pos hmem, if_pos hmem, hx0, hto0, inner_zero_left, hz, mul_zero]
        · rw [if_pos hmem, if_pos hmem, real_inner_smul_right,
            real_inner_comm (ξ (x n)) (toSpace (x n)),
            (CERW.Generic.Norm.subgradient_euler hΨ (hξ (x n) hx0)).1]
    rw [hQ, inner_add_right, hI, hdep, hsq]
    by_cases hmem : x n ∈ departureRange x n
    · rw [Finset.insert_eq_of_mem hmem, if_neg (not_not.mpr hmem)]
      push_cast
      linarith [ih]
    · rw [Finset.sum_insert hmem, if_pos hmem]
      push_cast
      linarith [ih]

/-- **`eq:quadratic` for a norm, almost surely.** For every walk with drift field `ξ` (a choice of
subgradients of the norm `Ψ` with `ξ 0 = 0`), almost surely, for every `n`,
`|X_n|² = n - 2ε Σ_{y ∈ A_n} Ψ(y) + 𝒬_n`. -/
theorem ae_sq_euclidNorm_eq_norm (hΨ : IsNorm Ψ) {ε : ℝ}
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → Site d}
    (hX : IsDriftCERW μ ε ξ X) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ, euclidNorm (X n ω) ^ 2 =
      n - 2 * ε * ∑ y ∈ departureRange (X · ω) n, Ψ (toSpace y) +
        CERW.Support.Norm.ContactEvent.quadraticMartingale d ε ξ (X · ω) n := by
  filter_upwards [CERW.Support.Norm.Section5Localization.ae_legal_of_isDriftCERW hX] with ω hω n
  have hp : CERW.Support.Norm.ContactEvent.PathTyping d (fun j => X j ω) := hω
  exact sq_euclidNorm_eq_norm hΨ ε hξ (x := fun j => X j ω) hp.1 hp.2 n

/-- **The process `𝒬` is the Dynkin martingale of `|·|²`.** For every walk with drift field `ξ`,
almost surely, for every `t`, the explicit process `𝒬_t = Σ_{j<t} 2 X_j · (X_{j+1} - X_j + ε I_j ξ(X_j))`
equals the Dynkin process of `|·|²` for the drift kernel. -/
theorem quadraticMartingale_ae_eq_driftDynkin (hd : 1 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ}
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → Site d}
    (hX : IsDriftCERW μ ε ξ X) :
    ∀ᵐ ω ∂μ, ∀ t : ℕ,
      CERW.Support.Norm.ContactEvent.quadraticMartingale d ε ξ (X · ω) t =
        CERW.Support.Drift.driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X t ω := by
  filter_upwards [CERW.Support.Norm.Section5Localization.ae_legal_of_isDriftCERW hX] with ω hω t
  have hp : CERW.Support.Norm.ContactEvent.PathTyping d (fun j => X j ω) := hω
  have h1 := sq_euclidNorm_eq_norm hΨ ε hξ (x := fun j => X j ω) hp.1 hp.2 t
  have h2 := sq_euclidNorm_eq_dynkin_norm hd hΨ ε hξ (fun j => X j ω) hp.1 t
  have h3 := CERW.Support.Drift.dynkinMart_driftStepProb_eq_driftDynkin hd ε ξ
    (fun z : Site d => euclidNorm z ^ 2) X t ω
  linarith

/-- **The Dynkin process of `|·|²` is a martingale.** Together with
`quadraticMartingale_ae_eq_driftDynkin`, this is the statement that `𝒬` is a martingale for the
natural filtration of the walk. -/
theorem martingale_driftDynkin_sq (hd : 1 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ))
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site d} (hX : IsDriftCERW μ ε ξ X) :
    Martingale (CERW.Support.Drift.driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X)
      (CERW.Support.Law.pathFiltration hX.measurable) μ := by
  refine CERW.Support.Drift.martingale_driftDynkin hd hε.le (fun z i => ?_) hX _
  by_cases hz : z = 0
  · have h : ε * |ξ z i| = 0 := by rw [hz, hξ0]; simp
    rw [h]
    positivity
  · have h := CERW.Generic.Norm.subgradient_abs_coord_le hΨ (hξ z hz) i
    calc ε * |ξ z i| ≤ ε * Ψ (coordVec i) := mul_le_mul_of_nonneg_left h hε.le
      _ ≤ 1 / (d : ℝ) := (hell i).le

/-! ## The inclusion form of the rates -/

/-- A site whose value of a nonnegative function is below the inner radius lies in the departure
range. -/
theorem mem_departureRange_of_lt_normInnerRadius {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ∀ y, 0 ≤ ψ y) (x : ℕ → Site d) (n : ℕ) {y : Site d}
    (hy : ψ (toSpace y) < normInnerRadius ψ x n) : y ∈ departureRange x n := by
  rw [← CERW.Support.Occupation.toSpace_mem_cellSet_iff]
  by_contra hnot
  have hbdd : BddBelow (ψ '' (cellSet x n)ᶜ) :=
    ⟨0, by
      rintro _ ⟨z, -, rfl⟩
      exact hψ z⟩
  exact absurd hy (not_lt.mpr (csInf_le hbdd ⟨toSpace y, hnot, rfl⟩))

/-- A site of the departure range has value at most the outer radius. -/
theorem le_normMaxRadius_of_mem (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (x : ℕ → Site d) (n : ℕ)
    {y : Site d} (hy : y ∈ departureRange x n) : ψ (toSpace y) ≤ normMaxRadius ψ x n := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
  exact Finset.le_sup' (fun j => ψ (toSpace (x j)))
    (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hj)))

/-- Splitting a power: `ρ^e₁ l^e₂ (r^a L^b) ≤ r^(a+e₁) L^(b+e₂)` for `ρ ≤ r`, `l ≤ L` and
nonnegative `e₁, e₂`. -/
theorem rpow_mul_le {r L ρ l : ℝ} (hρ : 0 < ρ) (hl : 0 < l) (hr : ρ ≤ r) (hL : l ≤ L)
    {a b e₁ e₂ : ℝ} (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) :
    ρ ^ e₁ * l ^ e₂ * (r ^ a * L ^ b) ≤ r ^ (a + e₁) * L ^ (b + e₂) := by
  have hr0 : 0 < r := lt_of_lt_of_le hρ hr
  have hL0 : 0 < L := lt_of_lt_of_le hl hL
  rw [Real.rpow_add hr0, Real.rpow_add hL0]
  have h1 : ρ ^ e₁ ≤ r ^ e₁ := Real.rpow_le_rpow hρ.le hr he₁
  have h2 : l ^ e₂ ≤ L ^ e₂ := Real.rpow_le_rpow hl.le hL he₂
  have h4 : 0 ≤ l ^ e₂ := (Real.rpow_pos_of_pos hl _).le
  have h5 : 0 ≤ r ^ e₁ := (Real.rpow_pos_of_pos hr0 _).le
  have h6 : 0 ≤ r ^ a * L ^ b := by positivity
  calc ρ ^ e₁ * l ^ e₂ * (r ^ a * L ^ b) ≤ r ^ e₁ * L ^ e₂ * (r ^ a * L ^ b) :=
        mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 h4 h5) h6
    _ = r ^ a * r ^ e₁ * (L ^ b * L ^ e₂) := by ring

/-- The arithmetic of the enlargement of the constant: if `m a_in ≤ a_out = L b₀` with `m > 0`,
then with `K = C₀ (1 + m⁻¹) + 1` one has `C₀ a_in ≤ L K b₀` and `C₀ a_out < L K b₀`. -/
theorem enlarged_constant_bounds {a_in a_out b₀ L m C₀ K : ℝ} (hain : 0 ≤ a_in)
    (haout : 0 < a_out) (hout : a_out = L * b₀) (hm : 0 < m) (hle : m * a_in ≤ a_out)
    (hC₀ : 0 < C₀) (hK : K = C₀ * (1 + m⁻¹) + 1) :
    C₀ * a_in ≤ L * (K * b₀) ∧ C₀ * a_out < L * (K * b₀) := by
  have hinv := inv_mul_cancel₀ hm.ne'
  have hKm : K * m = C₀ * (m + 1) + m := by
    rw [hK]
    calc (C₀ * (1 + m⁻¹) + 1) * m = C₀ * (m + m⁻¹ * m) + m := by ring
      _ = C₀ * (m + 1) + m := by rw [hinv]
  have hCK : C₀ < K := by
    have : 0 < C₀ * m⁻¹ := by positivity
    rw [hK]
    nlinarith
  have heq : L * (K * b₀) = K * a_out := by rw [hout]; ring
  rw [heq]
  constructor
  · calc C₀ * a_in ≤ (K * m) * a_in := by
          refine mul_le_mul_of_nonneg_right ?_ hain
          rw [hKm]
          nlinarith
      _ = K * (m * a_in) := by ring
      _ ≤ K * a_out := mul_le_mul_of_nonneg_left hle (by linarith)
  · exact mul_lt_mul_of_pos_right hCK haout

/-- **The enlarged constant of the inclusion form.** Let `r` be positive at `2` and nondecreasing
on `n ≥ 2`, and let `C₀ > 0`. There is `K > C₀`, depending only on `d`, `r 2` and `C₀`, such that for
every `n ≥ 2` the inner bound `C₀ a_in` is at most `(log n) K b_n` and the outer bound `C₀ a_out`
is less than `(log n) K b_n`, where `a_in = r^{3/4}(log n)^{1/4}` (`d = 2`) or `(r log n)^{1/2}`
(`d ≥ 3`), `a_out = r^{5/6}(log n)^{7/6}` (`d = 2`) or `r^{d/(d+1)}(log n)^{(d+2)/(d+1)}`
(`d ≥ 3`), and `b_n = r^{5/6}(log n)^{1/6}` (`d = 2`) or `r^{d/(d+1)}(log n)^{1/(d+1)}`
(`d ≥ 3`). -/
theorem exists_inclusion_constant (hd : 2 ≤ d) {r : ℕ → ℝ} (hr2 : 0 < r 2)
    (hrm : ∀ n : ℕ, 2 ≤ n → r 2 ≤ r n) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ K : ℝ, C₀ < K ∧ ∀ n : ℕ, 2 ≤ n →
      (C₀ * (if d = 2 then r n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4)
          else (r n * Real.log n) ^ ((1 : ℝ) / 2)) ≤
        Real.log n * (K * (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
          else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1)))) ∧
      C₀ * (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((7 : ℝ) / 6)
          else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ (((d : ℝ) + 2) / (d + 1))) <
        Real.log n * (K * (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
          else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1))))) := by
  have hlam : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases h2 : d = 2
  · obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = r 2 ^ ((1 : ℝ) / 12) * Real.log 2 ^ ((11 : ℝ) / 12) :=
      ⟨_, rfl⟩
    have hm : 0 < m := by rw [hmdef]; positivity
    refine ⟨C₀ * (1 + m⁻¹) + 1, ?_, fun n hn => ?_⟩
    · have : 0 < C₀ * m⁻¹ := by positivity
      nlinarith
    · have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
      have hL0 : 0 < Real.log n := Real.log_pos hn1
      have hLlam : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      have hr0 : 0 < r n := lt_of_lt_of_le hr2 (hrm n hn)
      simp only [if_pos h2]
      have hout : r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((7 : ℝ) / 6) =
          Real.log n * (r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)) := by
        have h76 : (7 : ℝ) / 6 = 1 + 1 / 6 := by norm_num
        rw [h76, Real.rpow_add hL0, Real.rpow_one]
        ring
      have hle : m * (r n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4)) ≤
          r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((7 : ℝ) / 6) := by
        have h := rpow_mul_le hr2 hlam (hrm n hn) hLlam (a := 3 / 4) (b := 1 / 4)
          (e₁ := 1 / 12) (e₂ := 11 / 12) (by norm_num) (by norm_num)
        have e1 : (3 : ℝ) / 4 + 1 / 12 = 5 / 6 := by norm_num
        have e2 : (1 : ℝ) / 4 + 11 / 12 = 7 / 6 := by norm_num
        rw [e1, e2] at h
        rw [hmdef]
        exact h
      exact enlarged_constant_bounds (by positivity) (by positivity) hout hm hle hC₀ rfl
  · have hd3 : 3 ≤ d := by omega
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd3
    have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
    obtain ⟨e₁, he₁⟩ : ∃ e₁ : ℝ, e₁ = (d : ℝ) / (d + 1) - 1 / 2 := ⟨_, rfl⟩
    obtain ⟨e₂, he₂⟩ : ∃ e₂ : ℝ, e₂ = ((d : ℝ) + 2) / (d + 1) - 1 / 2 := ⟨_, rfl⟩
    have he₁0 : 0 ≤ e₁ := by
      rw [he₁, sub_nonneg, le_div_iff₀ hd1]
      linarith
    have he₂0 : 0 ≤ e₂ := by
      rw [he₂, sub_nonneg, le_div_iff₀ hd1]
      linarith
    obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = r 2 ^ e₁ * Real.log 2 ^ e₂ := ⟨_, rfl⟩
    have hm : 0 < m := by rw [hmdef]; positivity
    refine ⟨C₀ * (1 + m⁻¹) + 1, ?_, fun n hn => ?_⟩
    · have : 0 < C₀ * m⁻¹ := by positivity
      nlinarith
    · have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
      have hL0 : 0 < Real.log n := Real.log_pos hn1
      have hLlam : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      have hr0 : 0 < r n := lt_of_lt_of_le hr2 (hrm n hn)
      simp only [if_neg h2]
      have hout : r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ (((d : ℝ) + 2) / (d + 1)) =
          Real.log n * (r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1))) := by
        have hexp : ((d : ℝ) + 2) / (d + 1) = 1 + 1 / (d + 1) := by
          rw [one_add_div hd1.ne']
          congr 1
          ring
        rw [hexp, Real.rpow_add hL0, Real.rpow_one]
        ring
      have hin : (r n * Real.log n) ^ ((1 : ℝ) / 2) =
          r n ^ ((1 : ℝ) / 2) * Real.log n ^ ((1 : ℝ) / 2) :=
        Real.mul_rpow hr0.le hL0.le
      have hle : m * (r n * Real.log n) ^ ((1 : ℝ) / 2) ≤
          r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ (((d : ℝ) + 2) / (d + 1)) := by
        have h := rpow_mul_le hr2 hlam (hrm n hn) hLlam (a := 1 / 2) (b := 1 / 2)
          (e₁ := e₁) (e₂ := e₂) he₁0 he₂0
        have e1 : (1 : ℝ) / 2 + e₁ = (d : ℝ) / (d + 1) := by rw [he₁]; ring
        have e2 : (1 : ℝ) / 2 + e₂ = ((d : ℝ) + 2) / (d + 1) := by rw [he₂]; ring
        rw [e1, e2] at h
        rw [hin, hmdef]
        exact h
      refine enlarged_constant_bounds (by positivity) (by positivity) hout hm hle hC₀ rfl

/-- **The inclusions follow from the radius bounds.** Let `ψ ≥ 0` and let `r` be positive at `2`
and nondecreasing on `n ≥ 2`. For every `C₀ > 0` there is `K > C₀` such that for every path `x` and
every `n ≥ 2`, if the inner radius is within `C₀ a_in` of `r_n` and the outer radius exceeds `r_n` by
at most `C₀ a_out`, then every lattice point with `ψ(y) < r_n - (log n) K b_n` is a departed site and
every departed site has `ψ(y) < r_n + (log n) K b_n`. -/
theorem inclusions_of_radius_bounds (hd : 2 ≤ d) {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ∀ y, 0 ≤ ψ y) {r : ℕ → ℝ} (hr2 : 0 < r 2) (hrm : ∀ n : ℕ, 2 ≤ n → r 2 ≤ r n)
    {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ K : ℝ, C₀ < K ∧ ∀ (x : ℕ → Site d) (n : ℕ), 2 ≤ n →
      |normInnerRadius ψ x n - r n| ≤
        C₀ * (if d = 2 then r n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4)
          else (r n * Real.log n) ^ ((1 : ℝ) / 2)) →
      normMaxRadius ψ x n - r n ≤
        C₀ * (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((7 : ℝ) / 6)
          else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ (((d : ℝ) + 2) / (d + 1))) →
      {y : Site d | ψ (toSpace y) < r n - Real.log n * (K * (if d = 2 then
          r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
          else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1))))} ⊆
          ↑(departureRange x n) ∧
        (↑(departureRange x n) : Set (Site d)) ⊆
          {y | ψ (toSpace y) < r n + Real.log n * (K * (if d = 2 then
            r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
            else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1))))} := by
  obtain ⟨K, hCK, hK⟩ := exists_inclusion_constant hd hr2 hrm hC₀
  refine ⟨K, hCK, fun x n hn hin hout => ?_⟩
  obtain ⟨h1, h2⟩ := hK n hn
  constructor
  · intro y hy
    refine mem_departureRange_of_lt_normInnerRadius hψ x n ?_
    have hlow := (abs_le.mp hin).1
    have hy' : ψ (toSpace y) < r n - Real.log n * (K * (if d = 2 then
          r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
          else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1)))) := hy
    linarith
  · intro y hy
    have hmem : y ∈ departureRange x n := Finset.mem_coe.mp hy
    have h3 := le_normMaxRadius_of_mem ψ x n hmem
    show ψ (toSpace y) < r n + Real.log n * (K * (if d = 2 then
          r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
          else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1))))
    linarith

/-- The radius `r_n = ((d+1) n/(2 d ε V))^{1/(d+1)}` is positive at `n = 2` and nondecreasing
on `n ≥ 2`. -/
theorem radius_two_pos_mono (hd : 1 ≤ d) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V) {r : ℕ → ℝ}
    (hr : ∀ n : ℕ, r n = ((d + 1) * n / (2 * d * ε * V)) ^ ((1 : ℝ) / (d + 1))) :
    0 < r 2 ∧ ∀ n : ℕ, 2 ≤ n → r 2 ≤ r n := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨?_, fun n hn => ?_⟩
  · rw [hr 2]
    positivity
  · rw [hr 2, hr n]
    have h2n : ((2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    gcongr

/-- The unit `b_n` of the bound on the local times is nonnegative. -/
theorem localTime_unit_nonneg {r : ℕ → ℝ} {n : ℕ} (hrn : 0 < r n) (hn : 2 ≤ n) :
    0 ≤ (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
      else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1))) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hL0 : 0 < Real.log n := Real.log_pos hn1
  split_ifs <;> positivity

/-- **The inclusion form of the rates, for a norm** (the paragraph after Theorem 2.1). Let `d ≥ 2`,
`Ψ` a norm, `ε > 0` with `ε Ψ(e_i) < 1/d`, and `p > 0`. There is `C > 0`, depending only on
`d, ε, Ψ, p`, such that for every choice of subgradients `ξ` with `ξ 0 = 0`, every walk with drift
field `ξ` and every `n ≥ 2`, with probability at least `1 - C n^{-p}` the following hold
simultaneously, where `B_n = C r_n^{5/6} (log n)^{1/6}` if `d = 2` and
`B_n = C r_n^{d/(d+1)} (log n)^{1/(d+1)}` if `d ≥ 3`: the local times satisfy
`|ℓ_n(x) - 2dε(r_n - Ψ(x))₊| ≤ B_n` for every site `x`; every lattice point `x` with
`Ψ(x) < r_n - (log n) B_n` lies in `A_n`; and `A_n ⊆ {x : Ψ(x) < r_n + (log n) B_n}`. -/
theorem norm_shape_rates_inclusions (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))
    ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ ((∀ x : Site d,
              |(localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - Ψ (toSpace x)) 0| ≤
                C * (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
                  else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1)))) ∧
            {x : Site d | Ψ (toSpace x) < r n - Real.log n * (C * (if d = 2 then
                r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
                else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1))))} ⊆
              ↑(departureRange (X · ω) n) ∧
            (↑(departureRange (X · ω) n) : Set (Site d)) ⊆
              {x | Ψ (toSpace x) < r n + Real.log n * (C * (if d = 2 then
                r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
                else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1))))})} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  intro r
  have hd1 : 1 ≤ d := by omega
  have hV := normBallVolume_pos_of_isNorm hd1 hΨ
  have hψ : ∀ y, 0 ≤ Ψ y := (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1
  obtain ⟨hr2, hrm⟩ := radius_two_pos_mono hd1 hε hV (r := r) (fun n => rfl)
  obtain ⟨C₀, hC₀, h⟩ := CERW.Frozen.norm_shape_rates.{u} hd Ψ hΨ ε hε hell p hp
  obtain ⟨K, hCK, hK⟩ := inclusions_of_radius_bounds hd hψ hr2 hrm hC₀
  refine ⟨K, hC₀.trans hCK, fun ξ hξ hξ0 Ω _ μ _ X hX n hn => ?_⟩
  refine le_trans (measure_mono ?_)
    ((h ξ hξ hξ0 μ X hX n hn).trans (ENNReal.ofReal_le_ofReal ?_))
  · intro ω hω hgood
    obtain ⟨hin, hout, hloc⟩ := hgood
    apply hω
    obtain ⟨h1, h2⟩ := hK (X · ω) n hn hin hout
    have hrn : 0 < r n := lt_of_lt_of_le hr2 (hrm n hn)
    refine ⟨fun x => (hloc x).trans ?_, h1, h2⟩
    exact mul_le_mul_of_nonneg_right hCK.le (localTime_unit_nonneg hrn hn)
  · have hnn : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    exact mul_le_mul_of_nonneg_right hCK.le hnn

/-- **The inclusion form of the rates, for the Minkowski functional of a convex body.** Let `d ≥ 2`,
`K` a compact convex set with the origin in its interior, `ψ = gauge K`, and `ε > 0` with
`ε ψ(±e_i) < 1/d`. For every `p > 0` there is `C > 0`, depending only on `d, ε, K, p`, such that for
every choice of subgradients `ξ` of `ψ` with `ξ 0 = 0`, every walk with drift field `ξ` and every
`n ≥ 2`, with probability at least `1 - C n^{-p}` the statements of `norm_shape_rates_inclusions`
hold with `ψ` in place of `Ψ` and `r_n = ((d+1) n/(2 d ε |K|))^{1/(d+1)}`. -/
theorem gauge_shape_rates_inclusions {K : Set (EuclideanSpace ℝ (Fin d))} (hd : 2 ≤ d)
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {p : ℝ} (hp : 0 < p) :
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * (volume K).toReal)) ^ ((1 : ℝ) / (d + 1))
    ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ ((∀ x : Site d,
              |(localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - gauge K (toSpace x)) 0| ≤
                C * (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
                  else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1)))) ∧
            {x : Site d | gauge K (toSpace x) < r n - Real.log n * (C * (if d = 2 then
                r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
                else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1))))} ⊆
              ↑(departureRange (X · ω) n) ∧
            (↑(departureRange (X · ω) n) : Set (Site d)) ⊆
              {x | gauge K (toSpace x) < r n + Real.log n * (C * (if d = 2 then
                r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
                else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1))))})} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  intro r
  have hd1 : 1 ≤ d := by omega
  have hV : 0 < (volume K).toReal := by
    rw [← normBallVolume_gauge hK hc h0]
    exact normBallVolume_gauge_pos hK hc h0
  have hψ : ∀ y, 0 ≤ gauge K y := fun y => gauge_nonneg y
  obtain ⟨hr2, hrm⟩ := radius_two_pos_mono hd1 hε hV (r := r) (fun n => rfl)
  obtain ⟨C₀, hC₀, h⟩ := CERW.Support.Norm.GaugeResults.gauge_rates hd hK hc h0 hε hell hp
  obtain ⟨K', hCK, hK'⟩ := inclusions_of_radius_bounds hd hψ hr2 hrm hC₀
  refine ⟨K', hC₀.trans hCK, fun ξ hξ hξ0 Ω _ μ _ X hX n hn => ?_⟩
  refine le_trans (measure_mono ?_)
    ((h ξ hξ hξ0 μ X hX n hn).trans (ENNReal.ofReal_le_ofReal ?_))
  · intro ω hω hgood
    obtain ⟨hin, hout, hloc⟩ := hgood
    apply hω
    obtain ⟨h1, h2⟩ := hK' (X · ω) n hn hin hout
    have hrn : 0 < r n := lt_of_lt_of_le hr2 (hrm n hn)
    refine ⟨fun x => (hloc x).trans ?_, h1, h2⟩
    exact mul_le_mul_of_nonneg_right hCK.le (localTime_unit_nonneg hrn hn)
  · have hnn : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    exact mul_le_mul_of_nonneg_right hCK.le hnn

end CERW.Support.Norm.NormGaugeConsequences
