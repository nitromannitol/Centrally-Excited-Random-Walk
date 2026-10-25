module

public import CERW.LimitShapes.KernelEvents

@[expose] public section

/-!
# Uniform prefix Freedman bounds

A finite union over deterministic times and lattice targets gives the martingale
estimate needed at the first exit time in Proposition `prop:coarse`.
-/

universe u

open CERW LatticeProb MeasureTheory

namespace CERW.LimitShapes.Exit

/-- Kernel Freedman bounds hold simultaneously at all prefixes and nearby targets. -/
theorem exists_uniform_kernel_freedman {d : ℕ} (hd : 2 ≤ d)
    (p : ℝ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      0 ≤ ε → (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X →
      ∀ N : ℕ, 2 ≤ N →
        μ {ω | ¬ ∀ t : ℕ, t ≤ N → ∀ y : Site d, euclidNorm y ≤ 3 * (N : ℝ) →
          |CERW.dynkinMart (CERW.driftStepProb d ε ξ)
            (fun z => CERW.latticeKernel d (z - y)) (X · ω) t| ≤
            C * (Real.sqrt (CERW.dynkinBracket (CERW.driftStepProb d ε ξ)
              (fun z => CERW.latticeKernel d (z - y))
              (fun z => CERW.latticeKernel d (z - y)) (X · ω) t * Real.log N) +
              Real.log N)} ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-p)) := by
  obtain ⟨A, hA, hF⟩ :=
    DynkinBounds.exists_dynkin_freedman_bound.{u} (p + d + 2) (by positivity)
  obtain ⟨_, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts_latticeKernel hd
  obtain ⟨Cg, hgrad⟩ := hK.gradBound
  have hCg := CERW.Support.Law.cg_nonneg (by omega : 1 ≤ d) hgrad
  let B := Cg + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hstep : ∀ y x e : Site d, e ∈ unitSteps d →
      |latticeKernel d (x + e - y) - latticeKernel d (x - y)| ≤ B := by
    intro y x e he
    rw [add_sub_right_comm]
    have hpow : (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [euclidNorm_nonneg (x - y)])
        (by have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
            linarith)
    exact (hgrad (x - y) e he).trans
      ((mul_le_mul_of_nonneg_left hpow hCg).trans (by dsimp [B]; linarith))
  let D : ℝ := 2 * 7 ^ d + 1
  let C := A * D * (B + 1)
  have hD : 1 ≤ D := by
    dsimp [D]
    linarith [pow_nonneg (show (0 : ℝ) ≤ 7 by norm_num) d]
  have hC : 0 < C := by dsimp [C]; positivity
  have hAC : A ≤ C := by
    dsimp [C]
    nlinarith [mul_le_mul_of_nonneg_left hD hA.le]
  have hABC : A * B ≤ C := by
    dsimp [C]
    nlinarith [mul_le_mul_of_nonneg_left hD hA.le]
  refine ⟨C, hC, ?_⟩
  intro ε ξ hε hξ Ω _ μ _ X hX N hN
  classical
  let Y := ballFinset d (3 * (N : ℝ))
  let T := (Finset.range (N + 1)).product Y
  let E : ℕ × Site d → Set Ω := fun a => {ω |
    ¬ |dynkinMart (driftStepProb d ε ξ) (fun z => latticeKernel d (z - a.2))
      (X · ω) a.1| ≤ A * (Real.sqrt (dynkinBracket (driftStepProb d ε ξ)
        (fun z => latticeKernel d (z - a.2)) (fun z => latticeKernel d (z - a.2))
        (X · ω) a.1 * Real.log N) + B * Real.log N)}
  have hsub : {ω | ¬ ∀ t : ℕ, t ≤ N → ∀ y : Site d, euclidNorm y ≤ 3 * (N : ℝ) →
      |dynkinMart (driftStepProb d ε ξ) (fun z => latticeKernel d (z - y))
        (X · ω) t| ≤ C * (Real.sqrt (dynkinBracket (driftStepProb d ε ξ)
          (fun z => latticeKernel d (z - y)) (fun z => latticeKernel d (z - y))
          (X · ω) t * Real.log N) + Real.log N)} ⊆ ⋃ a ∈ T, E a := by
    intro ω hbad
    simp only [Set.mem_setOf_eq, not_forall] at hbad
    obtain ⟨t, ht, y, hy, hbad⟩ := hbad
    simp only [Set.mem_iUnion]
    refine ⟨(t, y), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), mem_ballFinset_iff.mpr hy⟩, ?_⟩
    intro hgood
    apply hbad
    have hs := Real.sqrt_nonneg (dynkinBracket (driftStepProb d ε ξ)
      (fun z => latticeKernel d (z - y)) (fun z => latticeKernel d (z - y))
      (X · ω) t * Real.log N)
    have hl := Real.log_natCast_nonneg N
    change |dynkinMart _ _ _ _| ≤ _ at hgood ⊢
    nlinarith [mul_le_mul_of_nonneg_right hAC hs,
      mul_le_mul_of_nonneg_right hABC hl]
  have htail : ∀ a ∈ T, μ (E a) ≤
      ENNReal.ofReal (A * (N : ℝ) ^ (-(p + d + 2))) := by
    intro a ha
    have ht := Finset.mem_range.mp (Finset.mem_product.mp ha).1
    exact hF N hN a.1 (by omega) (by omega : 1 ≤ d) μ ε ξ hε hξ X hX
      (fun z => latticeKernel d (z - a.2)) B hB (hstep a.2)
  have hnR : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hn0 : (0 : ℝ) < N := by linarith
  have hcardY : (Y.card : ℝ) ≤ 7 ^ d * (N : ℝ) ^ d := by
    calc (Y.card : ℝ) ≤ (2 * (3 * (N : ℝ)) + 1) ^ d :=
        card_ballFinset_le d (by positivity)
      _ ≤ (7 * (N : ℝ)) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
      _ = 7 ^ d * (N : ℝ) ^ d := mul_pow _ _ d
  have hcard : (T.card : ℝ) ≤ (2 * 7 ^ d) * (N : ℝ) ^ (d + 2) := by
    change (((Finset.range (N + 1)).product Y).card : ℝ) ≤ _
    rw [Finset.product_eq_sprod, Finset.card_product, Finset.card_range,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    calc ((N : ℝ) + 1) * (Y.card : ℝ)
        ≤ (2 * N) * (7 ^ d * (N : ℝ) ^ d) :=
          mul_le_mul (by linarith) hcardY (by positivity) (by positivity)
      _ ≤ (2 * 7 ^ d) * (N : ℝ) ^ (d + 2) := by
        rw [pow_add, pow_two]
        nlinarith [pow_nonneg (show (0 : ℝ) ≤ 7 by norm_num) d,
          pow_nonneg hn0.le d, mul_nonneg (by positivity : 0 ≤ (7 : ℝ) ^ d)
            (mul_nonneg (pow_nonneg hn0.le d) (by nlinarith : 0 ≤ (N : ℝ)^2 - N))]
  have hpower : (N : ℝ) ^ (d + 2) * (N : ℝ) ^ (-(p + d + 2)) =
      (N : ℝ) ^ (-p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn0]
    congr 1
    push_cast
    ring
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le T E).trans ?_)
  calc ∑ a ∈ T, μ (E a)
      ≤ ∑ _a ∈ T, ENNReal.ofReal (A * (N : ℝ) ^ (-(p + d + 2))) :=
        Finset.sum_le_sum fun a ha => htail a ha
    _ = ENNReal.ofReal ((T.card : ℝ) * (A * (N : ℝ) ^ (-(p + d + 2)))) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-p)) := by
      apply ENNReal.ofReal_le_ofReal
      calc (T.card : ℝ) * (A * (N : ℝ) ^ (-(p + d + 2)))
          ≤ ((2 * 7 ^ d) * (N : ℝ) ^ (d + 2)) *
              (A * (N : ℝ) ^ (-(p + d + 2))) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = ((2 * 7 ^ d) * A) * (N : ℝ) ^ (-p) := by rw [← hpower]; ring
        _ ≤ C * (N : ℝ) ^ (-p) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          dsimp [C, D]
          nlinarith [mul_nonneg hA.le (by positivity : 0 ≤ (2 : ℝ) * 7 ^ d)]

end CERW.LimitShapes.Exit
