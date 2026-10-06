import CERW.Support.Norm.RadialNewtonConvolution
import CERW.Support.Guards.SourceEvents
import CERW.Support.Contact.ContactCell
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellSetVolume

/-!
# The contact convolution for the visited-cell set of the walk

`eq:contact-convolution` (`oct5.tex:768-771`) is applied in the source to the actual objects of
`sec:largest-ball` (`oct5.tex:633-655`): the cell set `D_n = ⋃_{x ∈ A_n} C_x` of the sites
visited before time `n`, the inner threshold `b = inf {Ψ(y) : y ∉ D_n}`, the set
`E = D_n ∖ {Ψ < b}`, a contact point `y₀` with `Ψ(y₀) = b` that is a limit of points outside `D_n`,
and `H = U_{D_n}(y₀)`. `RadialNewtonConvolution.contact_convolution_le_radial` proves the inequality
`(f * U_E)(y₀) ≤ ‖f‖₁ H` for a bounded measurable set `D` and a real `b` with `{Ψ < b} ⊆ D`, for
every nonnegative integrable radial function `f` and with no bound on `f`. This module supplies the
geometry from the definitions of the walk:

* `cellSet x n` is a finite union of unit cells of volume `|A_n|`: measurable
  (`measurableSet_cellSet`) and bounded (`isBounded_cellSet`).
* `normInnerRadius Ψ x n` is the infimum of `Ψ` over the complement of `D_n`
  (`isGLB_normInnerRadius`), `{Ψ < b} ⊆ D_n` (`sublevel_subset_cellSet`), and there is a contact
  point, a point of the closure of the complement with `Ψ(y₀) = b` (`exists_contact_point`, by
  compactness of the closure of the complement intersected with a sublevel set of the norm); at
  every contact point the closure of the cell of an unvisited site contains `y₀`
  (`exists_unvisited_cell_of_contact_point`).
* `ae_contact_convexity`: for almost every `v ∈ E`, `∇Ψ(v) · (v - y₀) ≥ Ψ(v) - b ≥ 0`
  (`eq:contact-convexity`).
* `contact_convolution_le_cellSet`: for every path and every `n`, at every `y₀` with
  `Ψ(y₀) = b`, with `E = D_n ∖ {Ψ < b}` and `H = U_{D_n}(y₀)`: the function
  `ζ ↦ f(ζ) U_E(y₀ - ζ)` is integrable, `(f * U_E)(y₀) ≤ ‖f‖₁ H` and `U_E(y₀) = H`.
  `source_contact_convolution` states the whole passage: the geometry, the existence of the
  contact point and the inequality at it.
* `contact_convolution_prob`: in the law of the walk with a drift field, with probability at least
  `1 - C n^{-p}`, at every contact point the convolution of `f` with `U_E` is at most
  `‖f‖₁ C r_n q_n`, by `contact_convolution_le_cellSet` and the proved probability consequence of the frozen `lem:contact`.

No step uses that the path takes unit steps, so no legality of the sample path is assumed; the
geometry and the inequality hold for every path `x : ℕ → ℤ^d` and every `n`. The probabilistic
statement uses the frozen `lem:contact` unchanged.
-/

universe u

open MeasureTheory LatticeProb

namespace CERW.Support.Norm.RadialNewtonSourceContact

open CERW CERW.Generic.Norm CERW.Support.Occupation CERW.Support.Contact
  CERW.Support.Norm.RadialNewtonConvolution

variable {d : ℕ}

/-! ## A minimizer of a norm over a closure -/

/-- A nonempty set `S ⊆ ℝ^d` has a point `y₀` in its closure at which a norm `Ψ` attains the
infimum of `Ψ` over `S`. The sublevel set `{Ψ ≤ inf + 1}` is bounded because `Ψ` dominates a
positive multiple of the Euclidean norm, so the closure of `S` meets it in a compact set. -/
theorem exists_mem_closure_eq_sInf (hd : 1 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {S : Set (EuclideanSpace ℝ (Fin d))} (hS : S.Nonempty) :
    ∃ y₀ ∈ closure S, Ψ y₀ = sInf (Ψ '' S) := by
  set b := sInf (Ψ '' S) with hb
  have hnn : ∀ y, 0 ≤ Ψ y := (map_zero_nonneg_neg hΨ).2.1
  have hbdd : BddBelow (Ψ '' S) := ⟨0, by rintro _ ⟨y, -, rfl⟩; exact hnn y⟩
  have hle : ∀ y ∈ S, b ≤ Ψ y := fun y hy => csInf_le hbdd ⟨y, hy, rfl⟩
  have hcont : Continuous Ψ := norm_continuous hΨ
  obtain ⟨hmin, hcoe⟩ := normMin_pos_mul_le hΨ hd
  have hlt : b < b + 1 := by linarith
  obtain ⟨_, ⟨y1, hy1, rfl⟩, h1⟩ := exists_lt_of_csInf_lt (hS.image Ψ) hlt
  have hFclosed : IsClosed (closure S ∩ {y | Ψ y ≤ b + 1}) :=
    isClosed_closure.inter (isClosed_le hcont continuous_const)
  have hFbdd : Bornology.IsBounded (closure S ∩ {y | Ψ y ≤ b + 1}) := by
    refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin d)))
      (r := (b + 1) / normMin Ψ)).subset fun y hy => ?_
    rw [mem_closedBall_zero_iff, le_div_iff₀ hmin]
    have := hcoe y
    have h2 : Ψ y ≤ b + 1 := hy.2
    nlinarith
  have hFc : IsCompact (closure S ∩ {y | Ψ y ≤ b + 1}) :=
    Metric.isCompact_of_isClosed_isBounded hFclosed hFbdd
  have hFne : (closure S ∩ {y | Ψ y ≤ b + 1}).Nonempty := ⟨y1, subset_closure hy1, h1.le⟩
  obtain ⟨y₀, hy₀F, hminOn⟩ := hFc.exists_isMinOn hFne hcont.continuousOn
  refine ⟨y₀, hy₀F.1, le_antisymm ?_ ?_⟩
  · refine le_of_not_gt fun hcon => ?_
    obtain ⟨_, ⟨y2, hy2, rfl⟩, h2⟩ := exists_lt_of_csInf_lt (hS.image Ψ) (lt_min hcon hlt)
    have hy2F : y2 ∈ closure S ∩ {y | Ψ y ≤ b + 1} :=
      ⟨subset_closure hy2, (h2.trans_le (min_le_right _ _)).le⟩
    have h3 : Ψ y₀ ≤ Ψ y2 := isMinOn_iff.mp hminOn y2 hy2F
    have h4 := h2.trans_le (min_le_left _ _)
    linarith
  · exact closure_minimal hle (isClosed_le continuous_const hcont) hy₀F.1

/-! ## The visited-cell set `D_n` -/

/-- The cell set `D_n` of a path is bounded: it lies in the open ball of radius
`H_n + √d`. -/
theorem isBounded_cellSet (hd : 1 ≤ d) (x : ℕ → Site d) (n : ℕ) :
    Bornology.IsBounded (cellSet x n) :=
  Metric.isBounded_ball.subset (cellSet_subset_ball hd x n)

/-- The complement of the cell set is nonempty, since `D_n` is bounded. -/
theorem compl_cellSet_nonempty (hd : 1 ≤ d) (x : ℕ → Site d) (n : ℕ) :
    (cellSet x n)ᶜ.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
  have hbdd : Bornology.IsBounded (Set.univ : Set (EuclideanSpace ℝ (Fin d))) := by
    rw [← h]
    exact isBounded_cellSet hd x n
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact NormedSpace.unbounded_univ ℝ _ hbdd

/-- **The inner threshold is the infimum.** `normInnerRadius Ψ x n` is the greatest lower bound of
`Ψ` over the complement of `D_n`, which is nonempty. It is the infimum of the source,
`b = inf {Ψ(y) : y ∈ ℝ^d ∖ D_n}`, and not the value of `sInf` at an empty or unbounded set. -/
theorem isGLB_normInnerRadius (hd : 1 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (x : ℕ → Site d) (n : ℕ) :
    IsGLB (Ψ '' (cellSet x n)ᶜ) (normInnerRadius Ψ x n) :=
  isGLB_csInf ((compl_cellSet_nonempty hd x n).image Ψ)
    ⟨0, by rintro _ ⟨y, -, rfl⟩; exact (map_zero_nonneg_neg hΨ).2.1 y⟩

/-- **`{Ψ < b} ⊆ D_n`.** -/
theorem sublevel_subset_cellSet {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (x : ℕ → Site d) (n : ℕ) :
    {v | Ψ v < normInnerRadius Ψ x n} ⊆ cellSet x n := by
  intro v hv
  by_contra hvD
  exact absurd (csInf_le ⟨0, by rintro _ ⟨y, -, rfl⟩; exact (map_zero_nonneg_neg hΨ).2.1 y⟩
    ⟨v, hvD, rfl⟩ : normInnerRadius Ψ x n ≤ Ψ v) (not_le.mpr hv)

/-- **The contact point.** There is a point `y₀` of the closure of `ℝ^d ∖ D_n` with
`Ψ(y₀) = b`: a limit of points outside `D_n` at which `Ψ` attains its infimum. -/
theorem exists_contact_point (hd : 1 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (x : ℕ → Site d) (n : ℕ) :
    ∃ y₀ : EuclideanSpace ℝ (Fin d), Ψ y₀ = normInnerRadius Ψ x n ∧
      y₀ ∈ closure (cellSet x n)ᶜ := by
  obtain ⟨y₀, hy₀, hΨy₀⟩ := exists_mem_closure_eq_sInf hd hΨ (compl_cellSet_nonempty hd x n)
  exact ⟨y₀, hΨy₀, hy₀⟩

/-- **The unvisited cell at a contact point.** If `y₀` lies in the closure of `ℝ^d ∖ D_n`, then it
lies in the closure of the cell `C_z` of a site `z` that has not been visited before time `n`; then
`ℓ_n(z) = 0`, `|z - y₀| ≤ √d/2`, and `Ψ(z) ≥ b` because `z` lies outside `D_n`. -/
theorem exists_unvisited_cell_of_contact_point {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) (x : ℕ → Site d) (n : ℕ) {y₀ : EuclideanSpace ℝ (Fin d)}
    (hcl : y₀ ∈ closure (cellSet x n)ᶜ) :
    ∃ z : Site d, localTime x n z = 0 ∧ y₀ ∈ closure (cell z) ∧
      ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2 ∧ normInnerRadius Ψ x n ≤ Ψ (toSpace z) := by
  obtain ⟨z, hzA, hzcl⟩ := exists_unvisited_mem_closure_cell x n hcl
  refine ⟨z, ?_, hzcl, ?_, ?_⟩
  · rwa [mem_departureRange_iff, not_lt, Nat.le_zero] at hzA
  · rw [norm_sub_rev]
    exact norm_sub_toSpace_le_of_mem_closure_cell hzcl
  · exact csInf_le ⟨0, by rintro _ ⟨y, -, rfl⟩; exact (map_zero_nonneg_neg hΨ).2.1 y⟩
      ⟨toSpace z, fun h => hzA ((toSpace_mem_cellSet_iff x n z).mp h), rfl⟩

/-! ## `eq:contact-convexity` -/

/-- **`eq:contact-convexity` at a point of differentiability.** If `Ψ` is differentiable at `v`,
then `∇Ψ(v) · (v - y₀) ≥ Ψ(v) - Ψ(y₀)`: Euler's relation `∇Ψ(v) · v = Ψ(v)` and the subgradient
inequality `∇Ψ(v) · y₀ ≤ Ψ(y₀)`. -/
theorem sub_le_inner_gradient_sub {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {v : EuclideanSpace ℝ (Fin d)} (hv : DifferentiableAt ℝ Ψ v) (y₀ : EuclideanSpace ℝ (Fin d)) :
    Ψ v - Ψ y₀ ≤ inner ℝ (gradient Ψ v) (v - y₀) := by
  have h1 := subgradient_euler hΨ (gradient_isSubgradient hΨ hv)
  rw [inner_sub_right, h1.1]
  have := h1.2 y₀
  linarith

/-- **`eq:contact-convexity`.** Let `D` be measurable, `E = D ∖ {Ψ < b}` and `Ψ(y₀) = b`. For almost
every `v ∈ E`, `∇Ψ(v) · (v - y₀) ≥ Ψ(v) - b ≥ 0`. A norm is differentiable almost everywhere
(Rademacher). -/
theorem ae_contact_convexity {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) {b : ℝ}
    {y₀ : EuclideanSpace ℝ (Fin d)} (hy₀ : Ψ y₀ = b) :
    ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict (D \ {v | Ψ v < b}),
      Ψ v - b ≤ inner ℝ (gradient Ψ v) (v - y₀) ∧ 0 ≤ Ψ v - b := by
  have hBm : MeasurableSet {v : EuclideanSpace ℝ (Fin d) | Ψ v < b} :=
    measurableSet_lt (norm_continuous hΨ).measurable measurable_const
  filter_upwards [ae_restrict_of_ae (ae_differentiableAt hΨ), ae_restrict_mem (hD.diff hBm)]
    with v hv hvE
  have h1 := sub_le_inner_gradient_sub hΨ hv y₀
  rw [hy₀] at h1
  exact ⟨h1, sub_nonneg.mpr (not_lt.mp hvE.2)⟩

/-! ## The contact convolution for the visited-cell set -/

/-- **`eq:contact-convolution` for the visited-cell set, at every point with `Ψ(y₀) = b`.**
Let `d ≥ 2`, let `Ψ` be a norm, `ε ≥ 0`, let `f` be a nonnegative integrable radial function on
`ℝ^d` (no bound, no moment, no measurable profile), let `x` be a path and `n` a time, let
`D_n = cellSet x n`, `b = normInnerRadius Ψ x n`, `E = D_n ∖ {Ψ < b}`, and let `y₀` satisfy
`Ψ(y₀) = b`. Then `ζ ↦ f(ζ) U_E(y₀ - ζ)` is integrable,
`(f * U_E)(y₀) ≤ ‖f‖₁ U_{D_n}(y₀)` and `U_E(y₀) = U_{D_n}(y₀)`. -/
theorem contact_convolution_le_cellSet (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 ≤ ε) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hrad : ∀ x y : EuclideanSpace ℝ (Fin d), ‖x‖ = ‖y‖ → f x = f y) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f) (x : ℕ → Site d) (n : ℕ) {y₀ : EuclideanSpace ℝ (Fin d)}
    (hy₀ : Ψ y₀ = normInnerRadius Ψ x n) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      f ζ * normPotential d ε Ψ (cellSet x n \ {v | Ψ v < normInnerRadius Ψ x n}) (y₀ - ζ)) ∧
    ∫ ζ : EuclideanSpace ℝ (Fin d),
        f ζ * normPotential d ε Ψ (cellSet x n \ {v | Ψ v < normInnerRadius Ψ x n}) (y₀ - ζ) ≤
      (∫ ζ : EuclideanSpace ℝ (Fin d), f ζ) * normPotential d ε Ψ (cellSet x n) y₀ ∧
    normPotential d ε Ψ (cellSet x n \ {v | Ψ v < normInnerRadius Ψ x n}) y₀ =
      normPotential d ε Ψ (cellSet x n) y₀ :=
  contact_convolution_le_radial hd hΨ hε hrad hf0 hfi (measurableSet_cellSet x n)
    (isBounded_cellSet (by omega) x n) (sublevel_subset_cellSet hΨ x n) hy₀

/-- **The passage of the source for the visited-cell set** (`oct5.tex:633-655, 759-771`). For every
path `x` and time `n`, with `D_n = cellSet x n` and `b = normInnerRadius Ψ x n`: `b` is the
infimum of `Ψ` over the complement of `D_n`, `{Ψ < b} ⊆ D_n`, and there is a contact point `y₀`,
that is a point of the closure of the complement with `Ψ(y₀) = b`, which lies in the closure of the
cell of an unvisited site, and at which, for every nonnegative integrable radial function `f`, the
function `ζ ↦ f(ζ) U_E(y₀ - ζ)` is integrable, `(f * U_E)(y₀) ≤ ‖f‖₁ H` with `H = U_{D_n}(y₀)`, and
`U_E(y₀) = H`. -/
theorem source_contact_convolution (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 ≤ ε) (x : ℕ → Site d) (n : ℕ) :
    IsGLB (Ψ '' (cellSet x n)ᶜ) (normInnerRadius Ψ x n) ∧
    {v | Ψ v < normInnerRadius Ψ x n} ⊆ cellSet x n ∧
    ∃ y₀ : EuclideanSpace ℝ (Fin d), Ψ y₀ = normInnerRadius Ψ x n ∧
      y₀ ∈ closure (cellSet x n)ᶜ ∧
      (∃ z : Site d, localTime x n z = 0 ∧ y₀ ∈ closure (cell z) ∧
        ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2 ∧ normInnerRadius Ψ x n ≤ Ψ (toSpace z)) ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ x y : EuclideanSpace ℝ (Fin d), ‖x‖ = ‖y‖ → f x = f y) → (∀ x, 0 ≤ f x) →
        Integrable f →
        Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
          f ζ * normPotential d ε Ψ (cellSet x n \ {v | Ψ v < normInnerRadius Ψ x n})
            (y₀ - ζ)) ∧
        ∫ ζ : EuclideanSpace ℝ (Fin d),
            f ζ * normPotential d ε Ψ (cellSet x n \ {v | Ψ v < normInnerRadius Ψ x n})
              (y₀ - ζ) ≤
          (∫ ζ : EuclideanSpace ℝ (Fin d), f ζ) * normPotential d ε Ψ (cellSet x n) y₀ ∧
        normPotential d ε Ψ (cellSet x n \ {v | Ψ v < normInnerRadius Ψ x n}) y₀ =
          normPotential d ε Ψ (cellSet x n) y₀ := by
  obtain ⟨y₀, hy₀, hcl⟩ := exists_contact_point (by omega : 1 ≤ d) hΨ x n
  exact ⟨isGLB_normInnerRadius (by omega) hΨ x n, sublevel_subset_cellSet hΨ x n, y₀, hy₀, hcl,
    exists_unvisited_cell_of_contact_point hΨ x n hcl,
    fun f hrad hf0 hfi => contact_convolution_le_cellSet hd hΨ hε hrad hf0 hfi x n hy₀⟩

/-! ## The contact convolution in the law of the walk -/

/-- **The contact convolution with probability `1 - C n^{-p}`** (`lem:contact` with
`eq:contact-convolution`). For every nonnegative integrable radial function `f` on `ℝ^d` (no bound,
no moment, no measurable profile), with probability at least `1 - C n^{-p}`: at every contact point
`y₀` (a point of the closure of `ℝ^d ∖ D_n` with `Ψ(y₀) = b`), the function
`ζ ↦ f(ζ) U_E(y₀ - ζ)` is integrable, `U_E(y₀) = U_{D_n}(y₀)`, and the convolution satisfies
`(f * U_E)(y₀) ≤ ‖f‖₁ U_{D_n}(y₀)` and `(f * U_E)(y₀) ≤ ‖f‖₁ C r_n q_n`. The constants and the
quantifiers are those of the frozen `lem:contact`, which is applied unchanged; the deterministic
part is `contact_convolution_le_cellSet`, valid for every sample path, so no legality of the
paths is assumed. -/
theorem contact_convolution_prob {d : ℕ} (hd : 2 ≤ d) :
    ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, IsNorm Ψ →
    ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) →
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))
    let q : ℕ → ℝ := fun n =>
      if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, n₀ ≤ n →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ x y : EuclideanSpace ℝ (Fin d), ‖x‖ = ‖y‖ → f x = f y) → (∀ x, 0 ≤ f x) →
        Integrable f →
        μ {ω | ¬ ∀ y₀ : EuclideanSpace ℝ (Fin d),
            Ψ y₀ = normInnerRadius Ψ (X · ω) n →
            y₀ ∈ closure (cellSet (X · ω) n)ᶜ →
            Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
              f ζ * normPotential d ε Ψ
                (cellSet (X · ω) n \ {v | Ψ v < normInnerRadius Ψ (X · ω) n}) (y₀ - ζ)) ∧
            normPotential d ε Ψ (cellSet (X · ω) n \ {v | Ψ v < normInnerRadius Ψ (X · ω) n}) y₀ =
              normPotential d ε Ψ (cellSet (X · ω) n) y₀ ∧
            ∫ ζ : EuclideanSpace ℝ (Fin d),
                f ζ * normPotential d ε Ψ
                  (cellSet (X · ω) n \ {v | Ψ v < normInnerRadius Ψ (X · ω) n}) (y₀ - ζ) ≤
              (∫ ζ : EuclideanSpace ℝ (Fin d), f ζ) *
                normPotential d ε Ψ (cellSet (X · ω) n) y₀ ∧
            ∫ ζ : EuclideanSpace ℝ (Fin d),
                f ζ * normPotential d ε Ψ
                  (cellSet (X · ω) n \ {v | Ψ v < normInnerRadius Ψ (X · ω) n}) (y₀ - ζ) ≤
              (∫ ζ : EuclideanSpace ℝ (Fin d), f ζ) * (C * r n * q n)}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  intro Ψ hΨ ε hε hell r q p hp
  obtain ⟨C, hC, n₀, h⟩ :=
    CERW.Support.Guards.SourceEvents.contact_potential_old_form hd Ψ hΨ ε hε hell p hp
  refine ⟨C, hC, n₀, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn f hrad hf0 hfi
  refine le_trans (measure_mono ?_) (h ξ hξ hξ0 μ X hX n hn)
  intro ω hω hQ
  refine hω fun y₀ hy₀ hcl => ?_
  obtain ⟨hint, hle, hUE⟩ :=
    contact_convolution_le_cellSet hd hΨ hε.le hrad hf0 hfi (X · ω) n hy₀
  exact ⟨hint, hUE, hle, hle.trans
    (mul_le_mul_of_nonneg_left (hQ y₀ hy₀ hcl) (integral_nonneg hf0))⟩

end CERW.Support.Norm.RadialNewtonSourceContact
