module

public import CERW.Generic.Harmonic.Maximum
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

/-! # Maximum principle on an exterior domain

Bounded annuli and decay at infinity give the exterior maximum principle used in
`eq:curvature-improved` and `sec:global-profile`.
-/

open Filter Topology InnerProductSpace Laplacian

namespace CERW.Generic.Harmonic

/-- A decaying harmonic function on an exterior domain is bounded by its inner boundary. -/
theorem harmonic_le_on_exterior {d : ℕ} (hd : 1 ≤ d)
    {R : ℝ} (hR : 0 < R) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hcont : Continuous f)
    (hharm : HarmonicOnNhd f {x : EuclideanSpace ℝ (Fin d) | R < ‖x‖})
    (hdecay : Filter.Tendsto f (Bornology.cobounded (EuclideanSpace ℝ (Fin d)))
      (nhds (0 : ℝ)))
    {M : ℝ} (hM : 0 ≤ M)
    (hboundary : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = R → f x ≤ M) :
    ∀ x : EuclideanSpace ℝ (Fin d), R ≤ ‖x‖ → f x ≤ M := by
  intro x hx
  rcases eq_or_lt_of_le hx with hx | hx
  · exact hboundary x hx.symm
  apply le_of_forall_pos_le_add
  intro ε hε
  have he := hdecay.eventually (gt_mem_nhds hε)
  obtain ⟨T, _, hT⟩ := (Filter.hasBasis_cobounded_norm.mem_iff).mp he
  let S := max T ‖x‖ + R
  let D := {y : EuclideanSpace ℝ (Fin d) | R < ‖y‖} ∩ {y | ‖y‖ < S}
  have hD : IsOpen D := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hb : Bornology.IsBounded D := by
    apply (Metric.isBounded_ball (x := (0 : EuclideanSpace ℝ (Fin d))) (r := S)).subset
    intro y hy
    exact Metric.mem_ball.mpr (by simpa only [dist_zero_right] using (show ‖y‖ < S from hy.2))
  have hf : ∀ y ∈ frontier D, f y ≤ M + ε := by
    intro y hy
    rcases frontier_inter_subset _ _ hy with hy | hy
    · have heq := frontier_lt_subset_eq continuous_const continuous_norm hy.1
      exact (hboundary y heq.symm).trans (le_add_of_nonneg_right hε.le)
    · have heq := frontier_lt_subset_eq continuous_norm continuous_const hy.2
      have hTy : T ≤ ‖y‖ := by
        change ‖y‖ = S at heq
        rw [heq]
        exact (le_max_left T ‖x‖).trans (by dsimp [S]; linarith [hR])
      exact (hT hTy).le.trans (by linarith)
  apply harmonic_le_of_boundary hd hD hb hcont.continuousOn
    (fun y hy => hharm y hy.1) hf x
  apply subset_closure
  exact ⟨hx, by dsimp [S]; linarith [le_max_right T ‖x‖, hR]⟩

end CERW.Generic.Harmonic
