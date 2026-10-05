import CERW.Support.Norm.GaugeShapeVolume
import CERW.Support.Norm.ConvexBodyShape

/-!
# The limit shape results for the Minkowski functional of a convex body, with their hypotheses

Let `d ≥ 2` and let `K ⊆ ℝ^d` be a compact convex set with the origin in its interior. Its Minkowski
functional `ψ = gauge K` is convex and positively homogeneous, and need not be even. Let `ε > 0`
satisfy `ε ψ(e_i) < 1/d` and `ε ψ(-e_i) < 1/d` for `1 ≤ i ≤ d`, let `ξ(x) ∈ ∂ψ(x)` be a choice of
subgradients at the sites `x ≠ 0`, with `ξ(0) = 0`, and let `X` be the centrally excited random
walk with drift field `ξ` (`IsDriftCERW μ ε ξ X`). Let `|K|` be the volume of `K` and
`r_n = ((d+1) n / (2 d ε |K|))^{1/(d+1)}`.

Theorem 2.1 (shape, local times, recurrence) and Proposition 5.1 (rates) hold for `ψ`, with the
volume `|K|` of the body in place of the volume of the unit ball of the norm. The statements below
are these results with the hypotheses above and no other:

* `gauge_limit_shape_inclusions`, `gauge_limit_shape_local_times`, `gauge_limit_shape_recurrence`
  and their conjunction `gauge_limit_shape`. Almost surely, for every `0 < η < 1` and all large
  `n`, the lattice points `x` with `ψ(x) < (1 - η) r_n` are departed sites and every departed site
  `x` has `ψ(x) < (1 + η) r_n`; for every `η > 0` and all large `n`, the local times satisfy
  `|ℓ_n(x) - 2 d ε (r_n - ψ(x))₊| ≤ η r_n` for every `x`; and every site is visited infinitely
  often. `gauge_limit_shape_local_times_sup` states the second part as the convergence to `0` of
  `r_n⁻¹ sup_x |ℓ_n(x) - 2 d ε (r_n - ψ(x))₊|`, together with the boundedness of the family.
* `gauge_rates`: for every `p > 0` there is `C > 0`, depending on `d, ε, K, p` only, such that for
  every choice of subgradients, every walk and every `n ≥ 2`, with probability at least
  `1 - C n^{-p}` the bounds of Proposition 5.1 on the inner radius, the outer radius and the local
  times hold simultaneously.
* `gauge_inner_radius_upper_bound`: the one-sided bound on the inner radius.
* `gauge_volume_limit`: `|A_n| / r_n^d` tends to `|K|` almost surely.
* `convex_body_limit_shape`: for the body `K` itself, a positive drift with the ellipticity, for
  every such drift a choice of subgradients and a walk, and, for every such choice and walk, the
  limit shape theorem with the dilates of the interior of `K`, together with the volume limit.

Each statement is obtained by applying `GaugeShapeEvents.gauge_shape_rates`,
`GaugeShapeEvents.gauge_shape`, `GaugeShapeEvents.gauge_inner_upper`,
`GaugeShapeVolume.gauge_shape_volume_body` and `ConvexBodyShape.isLimitShape_of_compact_convex`.
The coarse bounds, the local time potential lemma, the contact estimate and the projection events
of the Minkowski functional are consumed through their proofs; none of them is a hypothesis.
-/

universe u

open MeasureTheory Filter Topology
open scoped Pointwise
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.GaugeResults

open CERW CERW.Support.Norm.MinkowskiGauge CERW.Support.Norm.GaugeModel
  CERW.Support.Norm.GaugeShapeEvents CERW.Support.Norm.GaugeShapeVolume
  CERW.Support.Norm.ConvexBodyShape

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-- **Limit shape theorem, part (i), for the Minkowski functional of a convex body.** Almost
surely, for every `0 < η < 1` and all large `n`, the lattice points `x` with `ψ(x) < (1 - η) r_n`
are departed sites and every departed site `x` has `ψ(x) < (1 + η) r_n`, where
`r_n = ((d+1) n/(2 d ε |K|))^{1/(d+1)}` and `|K|` is the volume of the body. -/
theorem gauge_limit_shape_inclusions (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : IsDriftCERW μ ε ξ X) :
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * (volume K).toReal)) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
      {x : Site d | gauge K (toSpace x) < (1 - η) * r n} ⊆ ↑(departureRange (X · ω) n) ∧
        (↑(departureRange (X · ω) n) : Set (Site d)) ⊆
          {x | gauge K (toSpace x) < (1 + η) * r n} := by
  intro r
  have h := gauge_shape.{u} hd hK hc h0 hξ hξ0 hε hell μ X hX
  dsimp only at h
  rw [normBallVolume_gauge hK hc h0] at h
  exact h.mono fun ω hω => hω.1

/-- **Limit shape theorem, part (ii), for the Minkowski functional of a convex body.** Almost
surely, for every `η > 0` and all large `n`, `|ℓ_n(x) - 2 d ε (r_n - ψ(x))₊| ≤ η r_n` for every
`x ∈ ℤ^d`; that is, `r_n⁻¹ max_x |ℓ_n(x) - 2 d ε (r_n - ψ(x))₊|` tends to `0`. -/
theorem gauge_limit_shape_local_times (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : IsDriftCERW μ ε ξ X) :
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * (volume K).toReal)) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site d,
      |(localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - gauge K (toSpace x)) 0| ≤ η * r n := by
  intro r
  have h := gauge_shape.{u} hd hK hc h0 hξ hξ0 hε hell μ X hX
  dsimp only at h
  rw [normBallVolume_gauge hK hc h0] at h
  exact h.mono fun ω hω => hω.2.1

/-- **Limit shape theorem, part (ii), in the form of a limit of a supremum.** Almost surely, the
family `|ℓ_n(x) - 2 d ε (r_n - ψ(x))₊|`, `x ∈ ℤ^d`, is bounded for all large `n`, and
`r_n⁻¹ sup_x |ℓ_n(x) - 2 d ε (r_n - ψ(x))₊|` tends to `0` as `n → ∞`. -/
theorem gauge_limit_shape_local_times_sup (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : IsDriftCERW μ ε ξ X) :
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * (volume K).toReal)) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ, (∀ᶠ n : ℕ in atTop, BddAbove (Set.range fun x : Site d =>
        |(localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - gauge K (toSpace x)) 0|)) ∧
      Tendsto (fun n : ℕ => (1 / r n) * ⨆ x : Site d,
        |(localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - gauge K (toSpace x)) 0|)
      atTop (𝓝 0) := by
  intro r
  have hd1 : 1 ≤ d := by omega
  have hV : 0 < (volume K).toReal := by
    rw [← normBallVolume_gauge hK hc h0]
    exact normBallVolume_gauge_pos hK hc h0
  have h := gauge_limit_shape_local_times hd hK hc h0 hξ hξ0 hε hell μ X hX
  dsimp only at h
  filter_upwards [h] with ω hω
  refine ⟨(hω 1 one_pos).mono fun n hn => ⟨1 * r n, ?_⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hn x
  rw [Metric.tendsto_nhds]
  intro δ hδ
  filter_upwards [hω (δ / 2) (by positivity), eventually_ge_atTop 1] with n hn hn1
  have hr0 : 0 < r n := scale_pos hd1 hε hV hn1
  have hsup : (⨆ x : Site d, |(localTime (X · ω) n x : ℝ) -
      2 * d * ε * max (r n - gauge K (toSpace x)) 0|) ≤ δ / 2 * r n :=
    Real.iSup_le hn (by positivity)
  have hnn : 0 ≤ (1 / r n) * ⨆ x : Site d, |(localTime (X · ω) n x : ℝ) -
      2 * d * ε * max (r n - gauge K (toSpace x)) 0| :=
    mul_nonneg (by positivity) (Real.iSup_nonneg fun x => abs_nonneg _)
  have hle : (1 / r n) * ⨆ x : Site d, |(localTime (X · ω) n x : ℝ) -
      2 * d * ε * max (r n - gauge K (toSpace x)) 0| ≤ δ / 2 := by
    calc (1 / r n) * ⨆ x : Site d, |(localTime (X · ω) n x : ℝ) -
          2 * d * ε * max (r n - gauge K (toSpace x)) 0|
        ≤ (1 / r n) * (δ / 2 * r n) := mul_le_mul_of_nonneg_left hsup (by positivity)
      _ = δ / 2 := by field_simp
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

/-- **Limit shape theorem, part (iii), for the Minkowski functional of a convex body.** Almost
surely, the walk visits every site of `ℤ^d` infinitely often. -/
theorem gauge_limit_shape_recurrence (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : IsDriftCERW μ ε ξ X) :
    ∀ᵐ ω ∂μ, ∀ x : Site d, ∃ᶠ j in atTop, X j ω = x := by
  have h := gauge_shape.{u} hd hK hc h0 hξ hξ0 hε hell μ X hX
  dsimp only at h
  exact h.mono fun ω hω => hω.2.2

/-- **The limit shape theorem for the Minkowski functional of a convex body.** The conjunction of
parts (i), (ii) and (iii): `gauge_limit_shape_inclusions`, `gauge_limit_shape_local_times` and
`gauge_limit_shape_recurrence`. -/
theorem gauge_limit_shape (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : IsDriftCERW μ ε ξ X) :
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * (volume K).toReal)) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ,
      (∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
        {x : Site d | gauge K (toSpace x) < (1 - η) * r n} ⊆ ↑(departureRange (X · ω) n) ∧
          (↑(departureRange (X · ω) n) : Set (Site d)) ⊆
            {x | gauge K (toSpace x) < (1 + η) * r n}) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site d,
        |(localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - gauge K (toSpace x)) 0| ≤
          η * r n) ∧
      (∀ x : Site d, ∃ᶠ j in atTop, X j ω = x) := by
  intro r
  have h1 := gauge_limit_shape_inclusions hd hK hc h0 hξ hξ0 hε hell μ X hX
  have h2 := gauge_limit_shape_local_times hd hK hc h0 hξ hξ0 hε hell μ X hX
  have h3 := gauge_limit_shape_recurrence hd hK hc h0 hξ hξ0 hε hell μ X hX
  dsimp only at h1 h2
  filter_upwards [h1, h2, h3] with ω a b c
  exact ⟨a, b, c⟩

/-- **The rates for the Minkowski functional of a convex body.** For every `p > 0` there is
`C > 0`, depending on `d, ε, K, p` only (chosen before the choice of subgradients, the probability
space, the walk and `n`), such that for every choice of subgradients with `ξ(0) = 0`, every walk
`IsDriftCERW μ ε ξ X` and every `n ≥ 2`, with probability at least `1 - C n^{-p}` the three rates
hold simultaneously: for the inner radius `inf_{y ∉ D_n} ψ(y)`, for the outer radius
`max_{j ≤ n} ψ(X_j)` and for the local times against the cone `2 d ε (r_n - ψ)₊`. -/
theorem gauge_rates (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
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
        μ {ω | ¬ (|normInnerRadius (gauge K) (X · ω) n - r n|
                    ≤ C * (if d = 2 then r n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4)
                      else (r n * Real.log n) ^ ((1 : ℝ) / 2)) ∧
                  normMaxRadius (gauge K) (X · ω) n - r n
                    ≤ C * (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((7 : ℝ) / 6)
                      else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ (((d : ℝ) + 2) / (d + 1))) ∧
                  ∀ x : Site d,
                    |(localTime (X · ω) n x : ℝ)
                        - 2 * d * ε * max (r n - gauge K (toSpace x)) 0|
                      ≤ C * (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
                        else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1))))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  intro r
  have h := gauge_shape_rates.{u} hd hK hc h0 ε hε hell p hp
  dsimp only at h
  rw [normBallVolume_gauge hK hc h0] at h
  exact h

/-- **The one-sided bound on the inner radius for the Minkowski functional of a convex body.** For
every `p > 0` there is `C > 0`, chosen before the choice of subgradients, the probability space,
the walk and `n`, such that for every choice of subgradients with `ξ(0) = 0`, every walk
`IsDriftCERW μ ε ξ X` and every `n ≥ 2`, with probability at least `1 - C n^{-p}`,
`inf_{y ∉ D_n} ψ(y) - r_n ≤ C (r_n^{(3-d)/2} (log n)^{1/2} + 1)`. -/
theorem gauge_inner_radius_upper_bound (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
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
        μ {ω | ¬ (normInnerRadius (gauge K) (X · ω) n - r n ≤
            C * (r n ^ (((3 : ℝ) - d) / 2) * Real.log n ^ ((1 : ℝ) / 2) + 1))} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  intro r
  have h := gauge_inner_upper.{u} hd hK hc h0 ε hε hell p hp
  dsimp only at h
  rw [normBallVolume_gauge hK hc h0] at h
  exact h

/-- **The volume of the range for the Minkowski functional of a convex body.** Almost surely,
`|A_n| / r_n^d` tends to `|K|` as `n → ∞`, with `r_n = ((d+1) n/(2 d ε |K|))^{1/(d+1)}`. -/
theorem gauge_volume_limit (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : IsDriftCERW μ ε ξ X) :
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * (volume K).toReal)) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => ((departureRange (X · ω) n).card : ℝ) / r n ^ d) atTop
      (𝓝 (volume K).toReal) :=
  gauge_shape_volume_body.{u} hd hK hc h0 hξ hξ0 hε hell μ X hX

/-- **Every compact convex body with the origin in its interior is the limit shape of a centrally
excited random walk.** There is a positive drift `ε` with `ε ψ(±e_i) < 1/d`; for every positive
`ε` with this property there are a choice of subgradients `ξ(x) ∈ ∂ψ(x)`, `x ≠ 0`, `ξ(0) = 0`,
and a walk `IsDriftCERW μ ε ξ X`; and for every such choice and walk, almost surely the limit
shape theorem holds with the volume `|K|` in the scale and the dilates of the interior of `K` in
the inclusions, the local times follow the cone, every site is visited infinitely often, and
`|A_n| / r_n^d` tends to `|K|`. -/
theorem convex_body_limit_shape (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) :
    (0 < admissibleDrift d K ∧ Elliptic K (admissibleDrift d K)) ∧
    ∀ ε : ℝ, 0 < ε → Elliptic K ε →
      (∃ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
          (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X) ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X →
        let r : ℕ → ℝ := fun n =>
          ((d + 1) * n / (2 * d * ε * (volume K).toReal)) ^ ((1 : ℝ) / (d + 1))
        ∀ᵐ ω ∂μ,
          (∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
            {x : Site d | toSpace x ∈ ((1 - η) * r n) • interior K} ⊆
                ↑(departureRange (X · ω) n) ∧
              (↑(departureRange (X · ω) n) : Set (Site d)) ⊆
                {x | toSpace x ∈ ((1 + η) * r n) • interior K}) ∧
          (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site d,
            |(localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - gauge K (toSpace x)) 0| ≤
              η * r n) ∧
          (∀ x : Site d, ∃ᶠ j in atTop, X j ω = x) ∧
          Tendsto (fun n : ℕ => ((departureRange (X · ω) n).card : ℝ) / r n ^ d) atTop
            (𝓝 (volume K).toReal) := by
  obtain ⟨hadm, hbody⟩ := isLimitShape_of_compact_convex.{u} hd hK hc h0
  refine ⟨hadm, fun ε hε hell => ?_⟩
  obtain ⟨hex, hmain⟩ := hbody ε hε hell
  refine ⟨hex, fun ξ hξ hξ0 Ω _ μ _ X hX => ?_⟩
  intro r
  have h1 := hmain ξ hξ hξ0 μ X hX
  have h2 := gauge_volume_limit hd hK hc h0 hξ hξ0 hε hell μ X hX
  dsimp only at h1 h2
  filter_upwards [h1, h2] with ω a b
  exact ⟨a.1, a.2.1, a.2.2, b⟩

end CERW.Support.Norm.GaugeResults
