import CERW.Support.Norm.GaugeShapeEvents

/-!
# The volume of the range for the walk driven by the gauge of a convex body

Let `K ⊆ ℝ^d`, `d ≥ 2`, be a compact convex set with the origin in its interior, `ψ = gauge K` its
Minkowski functional, which need not be even, `ε > 0` with `ε ψ(±e_i) < 1/d`, and `ξ(x) ∈ ∂ψ(x)` an
arbitrary selection of subgradients with `ξ(0) = 0`. For the walk with drift opposite to `ξ`
(`IsDriftCERW`) and the scale `r_n = ((d+1) n/(2 d ε |B_ψ|))^{1/(d+1)}`, the source states right
after the limit shape theorem for a norm that its part (i) gives `|A_n|/r_n^d → |B_ψ|`; at the end
of the section on norms the same holds for the gauge of a convex body with `|K|` in place of
`|B_ψ|`.
This module proves the statement, almost surely, for the literal gauge:

* `gauge_shape_volume`: `|A_n| / r_n^d → |B_ψ|` almost surely, where `|A_n|` is the number of
  departed sites, `|B_ψ| = normBallVolume (gauge K)` and `r_n` is the scale of the shape theorem;
* `gauge_shape_volume_body`: the same limit is the volume `|K|` of the body.

The proof applies the limit shape theorem `GaugeShapeEvents.gauge_shape` (the shape (i): the range
lies between the sublevel sets `{ψ < (1 ∓ η) r_n}`), the identity `|D_n| = |A_n|` between the volume
of the cell set and the cardinality of the departure range, and the scaling `|{ψ < ρ}| = ρ^d |B_ψ|`.
The comparison between the lattice and the volumes is proved here: a point `v` of the cell of a site
`x` has `|ψ(v) - ψ(x)| ≤ Λ_ψ √d / 2`, so the cell set contains the sublevel set of height
`(1 - η) r_n - Λ_ψ √d/2` and lies in the sublevel set of height `(1 + η) r_n + Λ_ψ √d/2`; their
volumes are `|B_ψ|` times the `d`-th powers of these heights, and the ratio to `r_n^d` tends to
`|B_ψ|` as `η → 0`. No volume asymptotic and no shape statement enters as a premise.
-/

universe u

open MeasureTheory Filter Topology
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.GaugeShapeVolume

open CERW CERW.Support.Occupation CERW.Support.Norm.MinkowskiGauge CERW.Support.Norm.GaugeModel
  CERW.Support.Norm.GaugeCoarseVolume CERW.Support.Norm.GaugeShapeEvents

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-! ### The gauge on a cell -/

/-- A point of the cell of a site has gauge within `Λ_ψ √d / 2` of the gauge of the site. -/
private lemma abs_gauge_sub_le_of_mem_cell (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {x : Site d}
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ∈ cell x) :
    |gauge K v - gauge K (toSpace x)| ≤ normMax (gauge K) * (Real.sqrt d / 2) :=
  (abs_gauge_sub_le hK hc h0 v (toSpace x)).trans
    (mul_le_mul_of_nonneg_left (norm_sub_toSpace_le_of_mem_cell hv) (normMax_gauge_nonneg K))

/-- If every site of gauge below `s` has been departed from, the cell set contains the sublevel set
of height `s - Λ_ψ √d / 2`. -/
private lemma sublevel_subset_cellSet_of_lattice (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {s : ℝ} (X : ℕ → Site d) (n : ℕ)
    (h : {x : Site d | gauge K (toSpace x) < s} ⊆ ↑(departureRange X n)) :
    {v : EuclideanSpace ℝ (Fin d) | gauge K v < s - normMax (gauge K) * (Real.sqrt d / 2)} ⊆
      cellSet X n := by
  intro v hv
  have hvx : v ∈ cell (cellCenter v) := mem_cell_cellCenter v
  have h1 := (abs_le.mp (abs_gauge_sub_le_of_mem_cell hK hc h0 hvx)).1
  have hv' : gauge K v < s - normMax (gauge K) * (Real.sqrt d / 2) := hv
  have hxs : gauge K (toSpace (cellCenter v)) < s := by linarith
  have hxA : cellCenter v ∈ departureRange X n := h hxs
  exact Set.mem_iUnion₂.mpr ⟨cellCenter v, hxA, hvx⟩

/-- If every departed site has gauge below `s`, the cell set lies in the sublevel set of height
`s + Λ_ψ √d / 2`. -/
private lemma cellSet_subset_sublevel (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {s : ℝ} (X : ℕ → Site d) (n : ℕ)
    (h : (↑(departureRange X n) : Set (Site d)) ⊆ {x | gauge K (toSpace x) < s}) :
    cellSet X n ⊆
      {v : EuclideanSpace ℝ (Fin d) | gauge K v < s + normMax (gauge K) * (Real.sqrt d / 2)} := by
  intro v hv
  obtain ⟨x, hx, hvx⟩ := Set.mem_iUnion₂.mp hv
  have hxs : gauge K (toSpace x) < s := h hx
  have h1 := (abs_le.mp (abs_gauge_sub_le_of_mem_cell hK hc h0 hvx)).2
  show gauge K v < s + normMax (gauge K) * (Real.sqrt d / 2)
  linarith

/-! ### Cardinality and volume -/

/-- The number of departed sites is at least `|B_ψ|` times the `d`-th power of the height of the
sublevel set that the cell set contains. -/
private lemma card_ge_of_lattice (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (hd : 1 ≤ d) {s : ℝ}
    (hs : 0 < s - normMax (gauge K) * (Real.sqrt d / 2)) (X : ℕ → Site d) (n : ℕ)
    (h : {x : Site d | gauge K (toSpace x) < s} ⊆ ↑(departureRange X n)) :
    normBallVolume (gauge K) * (s - normMax (gauge K) * (Real.sqrt d / 2)) ^ d ≤
      ((departureRange X n).card : ℝ) :=
  normBallVolume_mul_pow_le_card_gauge hK h0 hd hs
    (sublevel_subset_cellSet_of_lattice hK hc h0 X n h)

/-- The number of departed sites is at most `|B_ψ|` times the `d`-th power of the height of the
sublevel set that contains the cell set. -/
private lemma card_le_of_lattice (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s)
    (X : ℕ → Site d) (n : ℕ)
    (h : (↑(departureRange X n) : Set (Site d)) ⊆ {x | gauge K (toSpace x) < s}) :
    ((departureRange X n).card : ℝ) ≤
      normBallVolume (gauge K) * (s + normMax (gauge K) * (Real.sqrt d / 2)) ^ d := by
  have hρ : 0 ≤ s + normMax (gauge K) * (Real.sqrt d / 2) := by
    have := normMax_gauge_nonneg K
    positivity
  have hV : 0 ≤ normBallVolume (gauge K) := by
    unfold normBallVolume
    exact ENNReal.toReal_nonneg
  have hsub := cellSet_subset_sublevel hK hc h0 X n h
  have hfin : volume {v : EuclideanSpace ℝ (Fin d) |
      gauge K v < s + normMax (gauge K) * (Real.sqrt d / 2)} ≠ ⊤ := by
    rw [volume_gauge_sublevel hK h0 hd hρ]
    exact ENNReal.ofReal_ne_top
  have h1 := ENNReal.toReal_mono hfin (measure_mono hsub)
  rw [volume_cellSet, ENNReal.toReal_natCast, volume_gauge_sublevel hK h0 hd hρ,
    ENNReal.toReal_ofReal (by positivity)] at h1
  linarith

/-! ### A ratio squeezed between two shifted powers -/

/-- If, for every `η ∈ (0, 1)` and all large `n`, `a n` lies between `V ((1 - η) r - δ)^d` and
`V ((1 + η) r + δ)^d`, with `r → ∞`, then `a n / r n ^ d → V`. -/
private lemma tendsto_div_pow_of_bounds {V δ : ℝ} (hV : 0 < V) (hδ : 0 ≤ δ) {a r : ℕ → ℝ}
    (hr : Tendsto r atTop atTop)
    (h : ∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
      V * ((1 - η) * r n - δ) ^ d ≤ a n ∧ a n ≤ V * ((1 + η) * r n + δ) ^ d) :
    Tendsto (fun n : ℕ => a n / r n ^ d) atTop (𝓝 V) := by
  rw [Metric.tendsto_nhds]
  intro ε' hε'
  set φ : ℝ → ℝ := fun η => max |V * (1 + 2 * η) ^ d - V| |V * (1 - 2 * η) ^ d - V| with hφ
  have hφc : Continuous φ := by
    have h1 : Continuous fun η : ℝ => V * (1 + 2 * η) ^ d := by fun_prop
    have h2 : Continuous fun η : ℝ => V * (1 - 2 * η) ^ d := by fun_prop
    exact ((h1.sub continuous_const).abs).max ((h2.sub continuous_const).abs)
  have hφ0 : φ 0 = 0 := by simp [hφ]
  obtain ⟨η₀, hη₀, hη₀φ⟩ := Metric.continuousAt_iff.mp hφc.continuousAt ε' hε'
  set η : ℝ := min (η₀ / 2) (1 / 4) with hη
  have hηpos : 0 < η := lt_min (by positivity) (by norm_num)
  have hη4 : η ≤ 1 / 4 := min_le_right _ _
  have hηlt : η < η₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hφη : φ η < ε' := by
    have h1 := hη₀φ (x := η) (by rw [Real.dist_eq, sub_zero, abs_of_pos hηpos]; exact hηlt)
    rw [hφ0, Real.dist_eq, sub_zero] at h1
    exact (le_abs_self _).trans_lt h1
  filter_upwards [h η hηpos (by linarith), hr.eventually_gt_atTop (δ / η)] with n hn hrn
  have hδη : 0 ≤ δ / η := by positivity
  have hr0 : 0 < r n := lt_of_le_of_lt hδη hrn
  have hδr : δ ≤ η * r n := by
    rw [div_lt_iff₀ hηpos] at hrn
    linarith
  obtain ⟨hlo, hhi⟩ := hn
  have hrd : 0 < r n ^ d := pow_pos hr0 d
  have hup : a n / r n ^ d ≤ V * (1 + 2 * η) ^ d := by
    rw [div_le_iff₀ hrd]
    calc a n ≤ V * ((1 + η) * r n + δ) ^ d := hhi
      _ ≤ V * ((1 + 2 * η) * r n) ^ d :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by nlinarith) d) hV.le
      _ = V * (1 + 2 * η) ^ d * r n ^ d := by rw [mul_pow]; ring
  have hlow : V * (1 - 2 * η) ^ d ≤ a n / r n ^ d := by
    rw [le_div_iff₀ hrd]
    have h12 : 0 ≤ (1 - 2 * η) * r n := mul_nonneg (by linarith) hr0.le
    calc V * (1 - 2 * η) ^ d * r n ^ d = V * ((1 - 2 * η) * r n) ^ d := by rw [mul_pow]; ring
      _ ≤ V * ((1 - η) * r n - δ) ^ d :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h12 (by nlinarith) d) hV.le
      _ ≤ a n := hlo
  rw [Real.dist_eq, abs_lt]
  have hA := le_max_left |V * (1 + 2 * η) ^ d - V| |V * (1 - 2 * η) ^ d - V|
  have hB := le_max_right |V * (1 + 2 * η) ^ d - V| |V * (1 - 2 * η) ^ d - V|
  have hA' := le_abs_self (V * (1 + 2 * η) ^ d - V)
  have hB' := neg_abs_le (V * (1 - 2 * η) ^ d - V)
  have hφ' : max |V * (1 + 2 * η) ^ d - V| |V * (1 - 2 * η) ^ d - V| < ε' := hφη
  constructor <;> linarith

/-! ### The volume of the range -/

/-- **`|A_n| / r_n^d → |B_ψ|` for the gauge of a convex body.** For `d ≥ 2`, a compact convex `K`
with the origin in its interior, `ε > 0` with `ε ψ(±e_i) < 1/d`, every choice of subgradients
`ξ(x) ∈ ∂ψ(x)` with `ξ(0) = 0` and every walk `IsDriftCERW μ ε ξ X`, almost surely the number of
departed sites `|A_n|`, divided by `r_n^d` for the scale
`r_n = ((d+1) n/(2 d ε |B_ψ|))^{1/(d+1)}`, tends to the volume `|B_ψ| = normBallVolume (gauge K)`
of the unit ball of the gauge. -/
theorem gauge_shape_volume (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : IsDriftCERW μ ε ξ X) :
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * normBallVolume (gauge K))) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => ((departureRange (X · ω) n).card : ℝ) / r n ^ d) atTop
      (𝓝 (normBallVolume (gauge K))) := by
  intro r
  have hd1 : 1 ≤ d := by omega
  have hV : 0 < normBallVolume (gauge K) := normBallVolume_gauge_pos hK hc h0
  have hr : Tendsto r atTop atTop := tendsto_coarseScale hd1 hε hV
  have hae := gauge_shape.{u} hd hK hc h0 hξ hξ0 hε hell μ X hX
  dsimp only at hae
  filter_upwards [hae] with ω hω
  obtain ⟨hincl, -, -⟩ := hω
  have hδ : 0 ≤ normMax (gauge K) * (Real.sqrt d / 2) :=
    mul_nonneg (normMax_gauge_nonneg K) (by positivity)
  refine tendsto_div_pow_of_bounds hV hδ hr (fun η hη0 hη1 => ?_)
  filter_upwards [hincl η hη0 hη1,
    hr.eventually_gt_atTop (normMax (gauge K) * (Real.sqrt d / 2) / (1 - η))] with n hn hrn
  obtain ⟨hlow, hhigh⟩ := hn
  have hη' : 0 < 1 - η := by linarith
  have hrpos : (1 - η) * r n - normMax (gauge K) * (Real.sqrt d / 2) > 0 := by
    rw [div_lt_iff₀ hη'] at hrn
    linarith
  have hr0 : 0 < r n := by
    by_contra hnot
    have : r n ≤ 0 := not_lt.mp hnot
    nlinarith
  refine ⟨card_ge_of_lattice hK hc h0 hd1 hrpos (fun j => X j ω) n hlow, ?_⟩
  exact card_le_of_lattice hK hc h0 hd1 (by positivity) (fun j => X j ω) n hhigh

/-- **`|A_n| / r_n^d → |K|`.** The limit of `gauge_shape_volume` is the volume of the body: for the
gauge of a compact convex body with the origin in its interior, `|B_ψ| = |K|`. -/
theorem gauge_shape_volume_body (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
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
      (𝓝 (volume K).toReal) := by
  intro r
  have h := gauge_shape_volume.{u} hd hK hc h0 hξ hξ0 hε hell μ X hX
  simp only [normBallVolume_gauge hK hc h0] at h
  exact h

/-! ### Consumption at bodies that are not symmetric -/

section Consumption

open CERW.Support.Norm.GaugePotential (cornerTriangle isCompact_cornerTriangle
  convex_cornerTriangle zero_mem_interior_cornerTriangle)
open CERW.Support.Norm.GaugeContactShape.Rates (cornerTriangle_ellipticity)

/-- **`|A_n| / r_n^d → |B_ψ| = |K|` at the cut disc, `ε = 1/4`.** The gauge of `cutDisc` (the disc
of radius `2` cut by `y₀ ≥ -1`) is not a norm. A subgradient selection and an actual walk
`IsDriftCERW μ (1/4) ξ X` exist, the body has positive area, and for every walk of this law, almost
surely the number of departed sites divided by `r_n²` tends to
`|B_ψ| = normBallVolume (gauge cutDisc)`, which is the area `|cutDisc|` of the body, with `r_n`
normalized by either of the two. -/
theorem cutDisc_shape_volume :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 → IsSubgradient (gauge cutDisc) (toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4 : ℝ) ξ X) ∧
      0 < (volume cutDisc).toReal ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4 : ℝ) ξ X →
      (let r : ℕ → ℝ := fun n =>
        ((((2 : ℕ) : ℝ) + 1) * n /
          (2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) * normBallVolume (gauge cutDisc))) ^
            ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => ((departureRange (X · ω) n).card : ℝ) / r n ^ 2) atTop
        (𝓝 (normBallVolume (gauge cutDisc)))) ∧
      (let r : ℕ → ℝ := fun n =>
        ((((2 : ℕ) : ℝ) + 1) * n /
          (2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) * (volume cutDisc).toReal)) ^
            ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => ((departureRange (X · ω) n).card : ℝ) / r n ^ 2) atTop
        (𝓝 (volume cutDisc).toReal)) := by
  have hK : IsCompact cutDisc := isCompact_cutDisc
  have hc : Convex ℝ cutDisc := convex_cutDisc
  have h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior cutDisc :=
    zero_mem_interior_cutDisc
  obtain ⟨ξ, hξ, hξ0, hwalk⟩ := exists_isDriftCERW_gauge (d := 2) (by norm_num)
    hc h0 (by norm_num) cutDisc_ellipticity
  refine ⟨ξ, hξ, hξ0, hwalk, ?_, fun μ _ X hX => ⟨?_, ?_⟩⟩
  · rw [← normBallVolume_gauge hK hc h0]
    exact normBallVolume_gauge_pos hK hc h0
  · exact gauge_shape_volume.{u} (le_refl 2) hK hc h0 hξ hξ0 (by norm_num)
      cutDisc_ellipticity μ X hX
  · exact gauge_shape_volume_body.{u} (le_refl 2) hK hc h0 hξ hξ0 (by norm_num)
      cutDisc_ellipticity μ X hX

/-- **`|A_n| / r_n^d → |B_ψ| = |K|` at the triangle with corners, `ε = 1/4`.** The gauge of the
triangle `cornerTriangle` with vertices `(-1,-1)`, `(2,-1)`, `(-1,2)` is not even and is not
differentiable along the ray through the vertex `(-1,-1)`. A subgradient selection and an actual
walk `IsDriftCERW μ (1/4) ξ X` exist, the body has positive area, and for every walk of this law,
almost surely the number of departed sites divided by `r_n²` tends to
`|B_ψ| = normBallVolume (gauge cornerTriangle)`, which is the area `|cornerTriangle|` of the body,
with `r_n` normalized by either of the two. -/
theorem cornerTriangle_shape_volume :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 → IsSubgradient (gauge cornerTriangle) (toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4 : ℝ) ξ X) ∧
      0 < (volume cornerTriangle).toReal ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4 : ℝ) ξ X →
      (let r : ℕ → ℝ := fun n =>
        ((((2 : ℕ) : ℝ) + 1) * n /
          (2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) * normBallVolume (gauge cornerTriangle))) ^
            ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => ((departureRange (X · ω) n).card : ℝ) / r n ^ 2) atTop
        (𝓝 (normBallVolume (gauge cornerTriangle)))) ∧
      (let r : ℕ → ℝ := fun n =>
        ((((2 : ℕ) : ℝ) + 1) * n /
          (2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) * (volume cornerTriangle).toReal)) ^
            ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => ((departureRange (X · ω) n).card : ℝ) / r n ^ 2) atTop
        (𝓝 (volume cornerTriangle).toReal)) := by
  have hK : IsCompact cornerTriangle := isCompact_cornerTriangle
  have hc : Convex ℝ cornerTriangle := convex_cornerTriangle
  have h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior cornerTriangle :=
    zero_mem_interior_cornerTriangle
  obtain ⟨ξ, hξ, hξ0, hwalk⟩ := exists_isDriftCERW_gauge (d := 2) (by norm_num)
    hc h0 (by norm_num) cornerTriangle_ellipticity
  refine ⟨ξ, hξ, hξ0, hwalk, ?_, fun μ _ X hX => ⟨?_, ?_⟩⟩
  · rw [← normBallVolume_gauge hK hc h0]
    exact normBallVolume_gauge_pos hK hc h0
  · exact gauge_shape_volume.{u} (le_refl 2) hK hc h0 hξ hξ0 (by norm_num)
      cornerTriangle_ellipticity μ X hX
  · exact gauge_shape_volume_body.{u} (le_refl 2) hK hc h0 hξ hξ0 (by norm_num)
      cornerTriangle_ellipticity μ X hX

end Consumption

end CERW.Support.Norm.GaugeShapeVolume
