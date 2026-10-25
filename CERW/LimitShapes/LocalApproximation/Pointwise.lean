module

public import CERW.Support.Norm.LocalTime
public import CERW.Support.Norm.ContactPotential

@[expose] public section

/-!
# Direct pointwise local-time approximation

The source-sum comparison uses Lemma `lem:cell` and distributional Laplacian growth.
-/

open LatticeProb CERW CERW.Support.Law CERW.Support.LocalTime CERW.Support.Drift

namespace CERW.LimitShapes.LocalApproximationProof

open private exists_abs_source_sum_sub_normPotential_le euclidNorm_sub_le_add
  from CERW.Support.Norm.LocalTime
open private one_add_log_div_log_three_nonneg log_four_mul_add_sqrt_add_two_le
  departureRange_bounds abs_le_max_mul_log abs_endpoint_add_source_le
  from CERW.Support.Norm.ContactPotential

/-- Dynkin's formula and the cell/Laplacian source sum give logarithmic pointwise error. -/
theorem exists_pointwise_bound {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {b : Site d → ℝ} {h : ℝ → ℝ} (hK : KernelFacts d b h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω), X 0 ω = 0 →
      (∀ j, euclidNorm (X j ω) ≤ j) → ∀ n : ℕ, 1 ≤ n → ∀ y : Site d,
      euclidNorm y ≤ 3 * n →
        |(localTime (fun j => X j ω) n y : ℝ) -
            normPotential d ε Ψ (cellSet (fun j => X j ω) n) (toSpace y) +
            driftDynkin ε ξ (fun z => b (z - y)) X n ω| ≤ C * (1 + ε) * Real.log (n + 2) := by
  obtain ⟨R, Ca, hR, hgradA⟩ := hK.gradAsymp
  obtain ⟨Cg, hgrad⟩ := hK.gradBound
  obtain ⟨Cb, hb⟩ := hK.growth
  obtain ⟨C_S, hCS, hsource⟩ :=
    exists_abs_source_sum_sub_normPotential_le hd hR hgradA hgrad hΨ
      CERW.Support.Norm.cell_gradient_holds
  set Cb' : ℝ := max Cb 0 with hCb'
  set K : ℝ := 1 + Real.log (4 + Real.sqrt d) / Real.log 3 with hK'
  have hCb'0 : 0 ≤ Cb' := le_max_right Cb 0
  have hKnn : 0 ≤ K := one_add_log_div_log_three_nonneg d
  refine ⟨(2 * Cb' + C_S) * K, mul_nonneg (by linarith) hKnn, ?_⟩
  intro ε hε ξ hξ hξ0 Ω X ω h0 hpath n hn y hy
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  set R' : ℝ := 4 * (n : ℝ) + Real.sqrt d with hR'
  set U : ℝ := normPotential d ε Ψ (cellSet (fun j => X j ω) n) (toSpace y) with hU
  rw [CERW.Support.Norm.ContactDynkin.localTime_eq_driftDynkin hK.poisson ε ξ hξ0 X ω h0 n y]
  set S : ℝ := ∑ x ∈ departureRange (fun j => X j ω) n, inner ℝ (ξ x) (centralDiff b (x - y))
    with hS
  have hgoal_eq : (b (X n ω - y) - b (-y) + ε * S - driftDynkin ε ξ (fun z => b (z - y)) X n ω) -
        U + driftDynkin ε ξ (fun z => b (z - y)) X n ω =
      b (X n ω - y) - b (-y) + (ε * S - U) := by ring
  rw [hgoal_eq]
  have hR'1 : 1 ≤ R' := by
    rw [hR']
    linarith
  have hsub : euclidNorm (X n ω - y) ≤ R' := by
    calc euclidNorm (X n ω - y) ≤ euclidNorm (X n ω) + euclidNorm y := euclidNorm_sub_le_add _ _
      _ ≤ (n : ℝ) + 3 * (n : ℝ) := add_le_add (hpath n) hy
      _ = 4 * (n : ℝ) := by ring
      _ ≤ R' := by rw [hR']; linarith
  have hneg : euclidNorm (-y) ≤ R' := by
    rw [CERW.Generic.Lattice.euclidNorm_neg]
    rw [hR']
    linarith
  have hb1 := abs_le_max_mul_log hb hsub
  have hb2 := abs_le_max_mul_log hb hneg
  have hsrc := hsource ε hε ξ hξ hξ0 (fun j => X j ω) n y R' hR'1
    (fun x hx => (departureRange_bounds (fun j => X j ω) hpath n hn y hy x hx).1)
  have hlogR' : 0 ≤ Real.log (R' + 2) := Real.log_nonneg (by linarith)
  have hcomb : |b (X n ω - y) - b (-y) + (ε * S - U)| ≤
      (2 * Cb' + C_S) * (1 + ε) * Real.log (R' + 2) :=
    abs_endpoint_add_source_le hb1 hb2 hsrc hCb'0 hCS hε hlogR'
  have hlogK : Real.log (R' + 2) ≤ K * Real.log ((n : ℝ) + 2) := by
    rw [hR', hK']
    exact log_four_mul_add_sqrt_add_two_le d n hn
  have hcoef : 0 ≤ (2 * Cb' + C_S) * (1 + ε) := by
    exact mul_nonneg (by linarith) (by linarith)
  calc |b (X n ω - y) - b (-y) + (ε * S - U)|
      ≤ (2 * Cb' + C_S) * (1 + ε) * Real.log (R' + 2) := hcomb
    _ ≤ (2 * Cb' + C_S) * (1 + ε) * (K * Real.log ((n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hlogK hcoef
    _ = (2 * Cb' + C_S) * K * (1 + ε) * Real.log ((n : ℝ) + 2) := by ring

end CERW.LimitShapes.LocalApproximationProof
