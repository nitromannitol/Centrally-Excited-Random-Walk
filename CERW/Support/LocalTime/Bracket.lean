import CERW.Support.Law.Dynkin
import CERW.Support.Occupation.FreshSum

/-!
# The bracket of the local-time martingale

`eq:bracket`: if `|b(x + e) - b(x)| ≤ C_g (1 + |x|)^{1-d}` for unit steps `e`, then the Dynkin
martingale `𝓜^y` of `b(X_j - y)` has increments at most `2 C_g (1 + |X_t - y|)^{1-d}` and
conditional variances at most `C_g² (1 + |X_t - y|)^{2-2d}`. Summed over time, the bracket is at
most `C_g² Σ_x ℓ_n(x) (1 + |x - y|)^{2-2d} = C_g² B_y`.
-/

namespace CERW.Support.LocalTime

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law
  CERW.Support.Occupation

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {ε : ℝ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d}

/-- The increments of `𝓜^y` are at most `2 C_g (1 + |X_t - y|)^{1-d}`, almost surely. -/
theorem ae_abs_dynkin_translate_succ_sub_le (hd : 1 ≤ d) (hε : 0 ≤ ε)
    (hεd : ε < 1 / (d : ℝ)) (hX : IsCERW μ ε X) {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (y : Site d) :
    ∀ᵐ ω ∂μ, ∀ t, |dynkin ε (fun z => b (z - y)) X (t + 1) ω -
      dynkin ε (fun z => b (z - y)) X t ω| ≤
        2 * (Cg * (1 + euclidNorm (X t ω - y)) ^ (1 - (d : ℝ))) := by
  filter_upwards [ae_abs_dynkin_succ_sub_le hd hε hεd hX (fun z => b (z - y))] with ω hω
  intro t
  exact hω t (Cg * (1 + euclidNorm (X t ω - y)) ^ (1 - (d : ℝ))) fun e he => by
    rw [add_sub_right_comm]
    exact hgrad (X t ω - y) e he

/-- The conditional variances of `𝓜^y` are at most `C_g² (1 + |X_t - y|)^{2-2d}`. -/
theorem condExp_sq_dynkin_translate_le (hd : 1 ≤ d) (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    (hX : IsCERW μ ε X) {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (y : Site d) (t : ℕ) :
    μ[fun ω => (dynkin ε (fun z => b (z - y)) X (t + 1) ω -
        dynkin ε (fun z => b (z - y)) X t ω) ^ 2 | pathFiltration hX.measurable t] ≤ᵐ[μ]
      fun ω => Cg ^ 2 * (1 + euclidNorm (X t ω - y)) ^ (2 - 2 * (d : ℝ)) := by
  have hCg : 0 ≤ Cg := by
    have h := hgrad 0 (unit ⟨0, by omega⟩) (mem_unitSteps.mpr ⟨⟨0, by omega⟩, Or.inl rfl⟩)
    have h' : |b (unit ⟨0, by omega⟩) - b 0| ≤ Cg := by simpa using h
    exact (abs_nonneg _).trans h'
  filter_upwards [condExp_sq_dynkin_succ_sub_le hd hε hεd hX (fun z => b (z - y)) t] with ω hω
  refine hω.trans ?_
  set ρ : ℝ := euclidNorm (X t ω - y) with hρ
  set B : ℝ := Cg * (1 + ρ) ^ (1 - (d : ℝ)) with hBdef
  have hbase : 0 ≤ (1 + ρ : ℝ) := by
    rw [hρ]
    linarith [euclidNorm_nonneg (X t ω - y)]
  have hB : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg hCg (Real.rpow_nonneg hbase _)
  have hterm : ∀ e ∈ unitSteps d, stepProb d ε (fun j => X j ω) t e *
        (b ((X t ω + e) - y) - b (X t ω - y)) ^ 2 ≤
      stepProb d ε (fun j => X j ω) t e * B ^ 2 := by
    intro e he
    refine mul_le_mul_of_nonneg_left ?_ (stepProb_nonneg hε hεd _ t e)
    have hosc := hgrad (X t ω - y) e he
    calc (b ((X t ω + e) - y) - b (X t ω - y)) ^ 2
        = (b ((X t ω - y) + e) - b (X t ω - y)) ^ 2 := by rw [add_sub_right_comm]
      _ = |b ((X t ω - y) + e) - b (X t ω - y)| ^ 2 := (sq_abs _).symm
      _ ≤ B ^ 2 := by
          rw [hBdef]
          exact pow_le_pow_left₀ (abs_nonneg _) hosc 2
  have hsum : ∑ e ∈ unitSteps d, stepProb d ε (fun j => X j ω) t e *
        (b ((X t ω + e) - y) - b (X t ω - y)) ^ 2 ≤ B ^ 2 := by
    calc ∑ e ∈ unitSteps d, stepProb d ε (fun j => X j ω) t e *
          (b ((X t ω + e) - y) - b (X t ω - y)) ^ 2
        ≤ ∑ e ∈ unitSteps d, stepProb d ε (fun j => X j ω) t e * B ^ 2 :=
            Finset.sum_le_sum hterm
      _ = B ^ 2 := by rw [← Finset.sum_mul, sum_stepProb hd ε _ t, one_mul]
  refine hsum.trans ?_
  have hsqrpow : ((1 + ρ) ^ (1 - (d : ℝ))) ^ 2 = (1 + ρ) ^ (2 - 2 * (d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase]
    congr 1
    push_cast
    ring
  rw [hBdef, mul_pow, hsqrpow]

/-- A sum over times of a function of the position is the local-time weighted sum over the
departure range. -/
theorem sum_range_eq_sum_localTime (x : ℕ → Site d) (n : ℕ) (g : Site d → ℝ) :
    ∑ j ∈ range n, g (x j) = ∑ z ∈ departureRange x n, (localTime x n z : ℝ) * g z := by
  classical
  rw [departureRange]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range n) (t := (Finset.range n).image x)
    (g := x) (f := fun i => g (x i)) (fun i hi => Finset.mem_image_of_mem x hi)]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hinner : ∑ i ∈ (Finset.range n).filter (fun i => x i = z), g (x i) =
      ∑ _i ∈ (Finset.range n).filter (fun i => x i = z), g z :=
    Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
  rw [localTime, hinner, Finset.sum_const, nsmul_eq_mul]

end CERW.Support.LocalTime
