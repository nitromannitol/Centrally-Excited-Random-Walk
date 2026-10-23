import CERW.Generic.Harmonic.LocalMaximum
import Mathlib.Topology.Order.Compact

/-! # The weak maximum principle

A positive quadratic perturbation forces a maximum onto the boundary of a bounded open set.
This provides the bounded-domain maximum principle needed for the paper's
`eq:curvature-improved` argument.
-/

open MeasureTheory Filter Topology
open InnerProductSpace Laplacian

namespace CERW.Generic.Harmonic

/-- A function with positive Laplacian cannot attain its maximum in the open set. -/
theorem le_boundary_of_laplacian_pos {d : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hcont : ContinuousOn f (closure D))
    (hdiff : ∀ x ∈ D, ContDiffAt ℝ 2 f x)
    (hlap : ∀ x ∈ D, 0 < laplacian f x)
    {M : ℝ} (hboundary : ∀ x ∈ frontier D, f x ≤ M) :
    ∀ x ∈ closure D, f x ≤ M := by
  intro x hx
  obtain ⟨y, hy, hmax⟩ := hDb.isCompact_closure.exists_isMaxOn ⟨x, hx⟩ hcont
  have hyfront : y ∈ frontier D := by
    rw [frontier, hD.interior_eq]
    refine ⟨hy, ?_⟩
    intro hyD
    have hm : IsLocalMax f y :=
      hmax.isLocalMax (Filter.mem_of_superset (hD.mem_nhds hyD) subset_closure)
    exact (not_lt_of_ge (laplacian_nonpos_of_localMax (hdiff y hyD) hm)) (hlap y hyD)
  exact (hmax hx).trans (hboundary y hyfront)

/-- A harmonic function on a bounded open set is bounded above by its boundary values. -/
theorem harmonic_le_of_boundary {d : ℕ} (hd : 1 ≤ d)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hcont : ContinuousOn f (closure D)) (hharm : HarmonicOnNhd f D)
    {M : ℝ} (hboundary : ∀ x ∈ frontier D, f x ≤ M) :
    ∀ x ∈ closure D, f x ≤ M := by
  obtain ⟨R, hR, hbound⟩ := hDb.closure.exists_pos_norm_le
  intro x hx
  apply le_of_forall_pos_le_add
  intro ε hε
  let η : ℝ := ε / (R ^ 2 + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  have hq : ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin d) => η * ‖y‖ ^ 2) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  have hpert := le_boundary_of_laplacian_pos hD hDb
    (hcont.add hq.continuous.continuousOn)
    (fun y hy => (hharm y hy).1.add hq.contDiffAt) (M := M + ε)
  have hlap : ∀ y ∈ D,
      0 < laplacian (fun z => f z + η * ‖z‖ ^ 2) y := by
    intro y hy
    have heq : (fun z : EuclideanSpace ℝ (Fin d) => f z + η * ‖z‖ ^ 2) =
        f + (fun z => η * ‖z‖ ^ 2) := rfl
    rw [heq, (hharm y hy).1.laplacian_add hq.contDiffAt]
    have hz : laplacian f y = 0 := (hharm y hy).2.self_of_nhds
    rw [hz, zero_add]
    have he : (fun z : EuclideanSpace ℝ (Fin d) => η * ‖z‖ ^ 2) =
        η • (fun z => ‖z‖ ^ 2) := rfl
    rw [he, laplacian_smul η (contDiff_norm_sq ℝ).contDiffAt, laplacian_norm_sq]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    exact mul_pos hη (mul_pos (by norm_num) hdpos)
  have hb : ∀ y ∈ frontier D, f y + η * ‖y‖ ^ 2 ≤ M + ε := by
    intro y hy
    have hn := hbound y (frontier_subset_closure hy)
    have hs : ‖y‖ ^ 2 ≤ R ^ 2 := sq_le_sq₀ (norm_nonneg _) hR.le |>.2 hn
    have hηR : η * (R ^ 2 + 1) = ε := by
      dsimp [η]
      exact div_mul_cancel₀ _ (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hs hη.le
    linarith [hboundary y hy]
  have hres := hpert hlap hb x hx
  change f x + η * ‖x‖ ^ 2 ≤ M + ε at hres
  have hnonneg : 0 ≤ η * ‖x‖ ^ 2 := mul_nonneg hη.le (sq_nonneg _)
  linarith

end CERW.Generic.Harmonic
