import CERW.Support.Norm.NormGaugeConsequences
import CERW.Support.Main.LimitShape

/-!
# The explicit quadratic process of `eq:quadratic` is a martingale

After the definition of the walk driven by the subgradients of a norm, the source displays the
process
`𝒬_t = Σ_{j<t} 2 X_j · (X_{j+1} - X_j + ε I_j ξ(X_j))`,
where `I_j` is the indicator that `X_j` is not among `X_0, …, X_{j-1}` (a first departure), states
that it is a martingale, and derives `eq:quadratic`,
`|X_n|² = n - 2ε Σ_{x ∈ A_n} Ψ(x) + 𝒬_n`.

In Lean the process is the finite sum `ContactEvent.quadraticMartingale d ε ξ X t`, with the
indicator `if X j ∉ departureRange X j then ξ (X j) else 0`. The module
`NormGaugeConsequences` proves, for the walk with drift field `ξ`, that `𝒬` equals the Dynkin
process of `|·|²` almost surely at all times simultaneously
(`quadraticMartingale_ae_eq_driftDynkin`) and that the Dynkin process is a martingale for the
natural filtration (`martingale_driftDynkin_sq`). It does not state that the explicit process is
itself a martingale; this module does, by two steps.

* `quadraticMartingale_congr`, `quadraticMartingale_eq_pastPath`: the explicit process at time `t`
  depends only on `X_0, …, X_t`. A term `j < t` involves `X_j`, `X_{j+1}` and the first-departure
  indicator, which involves `X_0, …, X_j`; all of these are positions up to time `t`.
* `stronglyAdapted_quadraticMartingale`: hence `𝒬_t` is a function of the past path, so it is
  strongly measurable for the natural filtration `ℱ_t = σ(X_0, …, X_t)`.
* `martingale_quadraticMartingale`: the explicit process is a martingale for the natural filtration,
  by the transfer `Martingale.congr` of the proved Dynkin martingale along the proved almost sure
  equality, for every walk with `IsDriftCERW μ ε ξ X`, a norm `Ψ`, `ε > 0` with
  `ε Ψ(e_i) < 1/d`, and a choice of subgradients `ξ(x) ∈ ∂Ψ(x)`, `x ≠ 0`, with `ξ 0 = 0`.
* `quadratic_identity_and_martingale`: `eq:quadratic` together with the martingale property.
* `quadraticMartingale_isCERW`: the same for the centrally excited random walk, `IsCERW μ ε X`,
  whose drift field is `x ↦ x/|x|`.

No adaptation, integrability, legality or martingale property is a premise: adaptation is proved
from the finite-prefix dependence, integrability is part of the transferred martingale, and the
legality of the paths holds almost surely by the proved `ae_legal_of_isDriftCERW`, used inside
`NormGaugeConsequences`.
-/

universe u

open MeasureTheory Filter
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.QuadraticProcessMartingale

open CERW CERW.Support.Law CERW.Support.Norm.ContactEvent CERW.Support.Norm.NormGaugeConsequences

variable {d : ℕ}

/-! ## The explicit process depends on the path up to time `t` only -/

/-- The value at time `t` of the explicit process is a function of the positions `X_0, …, X_t`:
two paths that agree up to time `t` have the same `𝒬_t`. Every term `j < t` of the sum involves
`X_j`, `X_{j+1}` and the set of departed sites `{X_0, …, X_{j-1}}`. -/
theorem quadraticMartingale_congr (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    {x y : ℕ → Site d} {t : ℕ} (h : ∀ j ≤ t, x j = y j) :
    quadraticMartingale d ε ξ x t = quadraticMartingale d ε ξ y t := by
  unfold quadraticMartingale
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjt : j < t := Finset.mem_range.mp hj
  have hdep : departureRange x j = departureRange y j := by
    unfold departureRange
    exact Finset.image_congr fun i hi => h i (by have := Finset.mem_range.mp hi; omega)
  rw [h j hjt.le, h (j + 1) hjt, hdep]

/-- The explicit process at time `t`, along the walk, is a function of the past path
`(X_0, …, X_t)`: `𝒬_t(ω) = G(X_0(ω), …, X_t(ω))` with
`G(p) = quadraticMartingale (extendPath p) t`. -/
theorem quadraticMartingale_eq_pastPath {Ω : Type*} (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (X : ℕ → Ω → Site d) (t : ℕ) :
    (fun ω => quadraticMartingale d ε ξ (fun j => X j ω) t) =
      fun ω => quadraticMartingale d ε ξ (extendPath (pastPath X t ω)) t := by
  funext ω
  exact quadraticMartingale_congr ε ξ fun j hj => (extendPath_pastPath X hj ω).symm

/-- The explicit process at time `t` is strongly measurable for `ℱ_t = σ(X_0, …, X_t)`. -/
theorem stronglyMeasurable_quadraticMartingale {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Site d} (hX : ∀ n, Measurable (X n)) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (t : ℕ) :
    StronglyMeasurable[pathFiltration hX t]
      (fun ω => quadraticMartingale d ε ξ (fun j => X j ω) t) := by
  rw [quadraticMartingale_eq_pastPath]
  exact stronglyMeasurable_comp_pastPath hX t
    (fun p => quadraticMartingale d ε ξ (extendPath p) t)

/-- The explicit process is adapted to the natural filtration of the walk. -/
theorem stronglyAdapted_quadraticMartingale {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Site d} (hX : ∀ n, Measurable (X n)) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) :
    StronglyAdapted (pathFiltration hX) (fun t ω => quadraticMartingale d ε ξ (fun j => X j ω) t) :=
  fun t => stronglyMeasurable_quadraticMartingale hX ε ξ t

/-- The explicit process starts at zero: the sum over `j < 0` is empty. -/
theorem quadraticMartingale_zero (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (x : ℕ → Site d) : quadraticMartingale d ε ξ x 0 = 0 := by
  simp [quadraticMartingale]

/-! ## The martingale property of the explicit process -/

/-- **The explicit process `𝒬` is a martingale** for the natural filtration `ℱ_t = σ(X_0, …, X_t)`
of the walk. Let `Ψ` be a norm on `ℝ^d`, `ε > 0` with `ε Ψ(e_i) < 1/d` for every coordinate
vector, `ξ(x) ∈ ∂Ψ(x)` for `x ≠ 0` with `ξ 0 = 0`, and let `X` be the walk with drift field `ξ`
on a probability space. Then `t ↦ Σ_{j<t} 2 X_j · (X_{j+1} - X_j + ε I_j ξ(X_j))` is a martingale.
The proof transfers the proved Dynkin martingale of `|·|²` along the proved almost sure equality
of the two processes (`Martingale.congr`), after proving that the explicit process is adapted. -/
theorem martingale_quadraticMartingale (hd : 1 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ))
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site d} (hX : IsDriftCERW μ ε ξ X) :
    Martingale (fun t ω => quadraticMartingale d ε ξ (fun j => X j ω) t)
      (pathFiltration hX.measurable) μ := by
  have hM := martingale_driftDynkin_sq hd hΨ hε hell hξ hξ0 hX
  have hae := quadraticMartingale_ae_eq_driftDynkin hd hΨ hξ hX
  refine hM.congr (stronglyAdapted_quadraticMartingale hX.measurable ε ξ) fun t => ?_
  filter_upwards [hae] with ω hω
  exact (hω t).symm

/-- **`eq:quadratic` with the martingale property.** Under the hypotheses of
`martingale_quadraticMartingale`, almost surely, for every `n`,
`|X_n|² = n - 2ε Σ_{y ∈ A_n} Ψ(y) + 𝒬_n`, and `𝒬` is a martingale for the natural filtration. -/
theorem quadratic_identity_and_martingale (hd : 1 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ))
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site d} (hX : IsDriftCERW μ ε ξ X) :
    (∀ᵐ ω ∂μ, ∀ n : ℕ, euclidNorm (X n ω) ^ 2 =
      n - 2 * ε * ∑ y ∈ departureRange (X · ω) n, Ψ (toSpace y) +
        quadraticMartingale d ε ξ (X · ω) n) ∧
    Martingale (fun t ω => quadraticMartingale d ε ξ (fun j => X j ω) t)
      (pathFiltration hX.measurable) μ :=
  ⟨ae_sq_euclidNorm_eq_norm hΨ hξ hX, martingale_quadraticMartingale hd hΨ hε hell hξ hξ0 hX⟩

/-! ## The centrally excited random walk -/

/-- **`eq:quadratic` and the martingale property for the centrally excited random walk.** For
`d ≥ 1`, `0 < ε < 1/d` and a process `X` with `IsCERW μ ε X` on a probability space, whose drift
field is `x ↦ x/|x|`: almost surely, for every `n`,
`|X_n|² = n - 2ε Σ_{y ∈ A_n} |y| + 𝒬_n`, and
`𝒬_t = Σ_{j<t} 2 X_j · (X_{j+1} - X_j + ε I_j X_j/|X_j|)` is a martingale for the natural
filtration of the walk. -/
theorem quadraticMartingale_isCERW (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) :
    (∀ᵐ ω ∂μ, ∀ n : ℕ, euclidNorm (X n ω) ^ 2 =
      n - 2 * ε * ∑ y ∈ departureRange (X · ω) n, euclidNorm y +
        quadraticMartingale d ε (fun z => unitDir (toSpace z)) (X · ω) n) ∧
    Martingale (fun t ω => quadraticMartingale d ε (fun z => unitDir (toSpace z))
        (fun j => X j ω) t) (pathFiltration hX.measurable) μ := by
  obtain ⟨hΨ, hsub, hξ0, hell⟩ := CERW.Support.Main.euclidean_norm_hypotheses (d := d) hεd
  have hXd : IsDriftCERW μ ε (fun z => unitDir (toSpace z)) X :=
    (CERW.Support.Drift.isCERW_iff_isDriftCERW μ ε X).1 hX
  have hell' : ∀ i : Fin d, ε * (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (coordVec i) <
      1 / (d : ℝ) := hell
  obtain ⟨h1, h2⟩ := quadratic_identity_and_martingale hd hΨ hε hell' hsub hξ0 hXd
  refine ⟨?_, h2⟩
  filter_upwards [h1] with ω hω n
  simpa only [norm_toSpace] using hω n

end CERW.Support.Norm.QuadraticProcessMartingale
