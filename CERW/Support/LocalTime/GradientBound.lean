import CERW.Model.Kernel
import LatticeProb.Walk.GRGrad
import LatticeProb.Walk.SRWGreenGrad
import LatticeProb.Walk.GreenPointwise

/-!
# The one-step bound for the potential kernel

The second estimate of `eq:gradient`: `|b(x + e) - b(x)| ≤ C_d (1 + |x|)^{1-d}` for every site
`x` and unit step `e`. For `d ≥ 3`, `b = -G` and this is the library's gradient bound for `G`,
stated with the `ℓ¹` norm, which dominates the Euclidean norm. For the planar kernel, `b` is the
limit of the partial sums `G_M(0) - G_M(x)`, and the library's bound for `G_M` is uniform in `M`,
so it passes to the limit.
-/

namespace CERW.Support.LocalTime

open Filter Topology LatticeProb CERW

variable {d : ℕ}

/-- A unit step from `x` is a neighbour of `x`. -/
lemma add_mem_nbrFinset_of_mem_unitSteps {x e : Site d} (he : e ∈ unitSteps d) :
    x + e ∈ nbrFinset x := by
  rw [mem_unitSteps] at he
  obtain ⟨i, hi | hi⟩ := he
  · rw [hi]
    simp only [nbrFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, by simp⟩
  · rw [hi]
    simp only [nbrFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, by simp [sub_eq_add_neg]⟩

/-- For `d ≥ 1` the `ℓ¹` power `(1 + |x|₁)^{1-d}` is at most the Euclidean power
`(1 + |x|)^{1-d}`, because `|x| ≤ |x|₁` and the exponent is nonpositive. -/
lemma rpow_graphNorm_le_rpow_euclidNorm (x : Site d) (hd : 1 ≤ d) :
    (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) ≤
      (1 + euclidNorm x) ^ (1 - (d : ℝ)) := by
  apply Real.rpow_le_rpow_of_nonpos
  · linarith [euclidNorm_nonneg x]
  · linarith [euclidNorm_le_graphNorm x]
  · have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith

/-- For `d ≥ 3`, `|G(x + e) - G(x)| ≤ C (1 + |x|)^{1-d}` for every unit step `e`. -/
theorem exists_abs_srwGreenInf_add_sub_le (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ x e : Site d, e ∈ unitSteps d →
      |srwGreenInf d (x + e) - srwGreenInf d x| ≤ C * (1 + euclidNorm x) ^ (1 - (d : ℝ)) := by
  obtain ⟨C, hCpos, hgrad⟩ := LatticeProb.exists_srwGreenInf_gradient d hd
  refine ⟨C, hCpos, fun x e he => ?_⟩
  have hmem : x + e ∈ nbrFinset x := add_mem_nbrFinset_of_mem_unitSteps he
  rw [abs_sub_comm]
  calc |srwGreenInf d x - srwGreenInf d (x + e)|
      ≤ C * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) := hgrad x (x + e) hmem
    _ ≤ C * (1 + euclidNorm x) ^ (1 - (d : ℝ)) :=
        mul_le_mul_of_nonneg_left (rpow_graphNorm_le_rpow_euclidNorm x (by omega)) hCpos.le

/-- For `d ≥ 2`, if `b(x)` is the limit of `G_M(0) - G_M(x)` for every `x`, then
`|b(x + e) - b(x)| ≤ C (1 + |x|)^{1-d}` for every unit step `e`. -/
theorem exists_abs_add_sub_le_of_tendsto (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : Site d → ℝ,
      (∀ x, Tendsto (fun M : ℕ => srwGreen d M 0 - srwGreen d M x) atTop (𝓝 (b x))) →
      ∀ x e : Site d, e ∈ unitSteps d →
        |b (x + e) - b x| ≤ C * (1 + euclidNorm x) ^ (1 - (d : ℝ)) := by
  obtain ⟨C, hCpos, hgrad⟩ := LatticeProb.exists_srwGreen_gradient d hd
  refine ⟨C, hCpos, fun b hb x e he => ?_⟩
  have hmem : x + e ∈ nbrFinset x := add_mem_nbrFinset_of_mem_unitSteps he
  have htend : Tendsto (fun M : ℕ => srwGreen d M x - srwGreen d M (x + e)) atTop
      (𝓝 (b (x + e) - b x)) := by
    have hEq : (fun M : ℕ => srwGreen d M x - srwGreen d M (x + e)) =
        (fun M : ℕ => (srwGreen d M 0 - srwGreen d M (x + e)) -
          (srwGreen d M 0 - srwGreen d M x)) := by
      funext M
      ring
    rw [hEq]
    exact (hb (x + e)).sub (hb x)
  have hbound : ∀ M : ℕ, |srwGreen d M x - srwGreen d M (x + e)| ≤
      C * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) :=
    fun M => hgrad M x (x + e) hmem
  have hle : |b (x + e) - b x| ≤ C * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) :=
    le_of_tendsto' htend.abs hbound
  calc |b (x + e) - b x|
      ≤ C * (1 + (graphNorm x : ℝ)) ^ (1 - (d : ℝ)) := hle
    _ ≤ C * (1 + euclidNorm x) ^ (1 - (d : ℝ)) :=
        mul_le_mul_of_nonneg_left (rpow_graphNorm_le_rpow_euclidNorm x (by omega)) hCpos.le

end CERW.Support.LocalTime
