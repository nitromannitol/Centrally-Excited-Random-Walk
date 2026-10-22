import CERW.LimitShapes.DynkinBounds
import CERW.LimitShapes.ShiftedSquare

/-!
# The kernel and shifted-square Freedman events

A union bound over the lattice ball of radius `3n` produces the two actual-bracket
martingale constituents of `sec:norm-event`. Their constants are uniform in the
subgradient field and the realization of the walk.
-/

universe u

open MeasureTheory ProbabilityTheory Filter LatticeProb

namespace CERW.LimitShapes.KernelEvents

open CERW CERW.Support.Drift CERW.LimitShapes.DynkinBounds

/-- Freedman bounds for the polynomial family of test functions indexed by targets
within distance `3n`, with an arbitrary positive deterministic increment scale. -/
private theorem exists_family_bound {d : ℕ} (hd : 1 ≤ d) (p : ℝ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → Site d → Site d → ℝ) (B : ℕ → ℝ),
      (∀ n : ℕ, 2 ≤ n → 0 < B n) →
      (∀ n : ℕ, 2 ≤ n → ∀ y x e : Site d, e ∈ unitSteps d →
        |f n y (x + e) - f n y x| ≤ B n) →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)),
        0 ≤ ε → (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) →
      ∀ (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ ∀ y : Site d, euclidNorm y ≤ 3 * n →
          |dynkinMart (driftStepProb d ε ξ) (f n y) (X · ω) n| ≤
            C * (Real.sqrt (dynkinBracket (driftStepProb d ε ξ) (f n y) (f n y)
              (X · ω) n * Real.log n) + B n * Real.log n)} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨A, hA, hF⟩ := exists_dynkin_freedman_bound.{u} (p + d) (by positivity)
  let C := A * ((7 : ℝ) ^ d + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hAC : A ≤ C := by
    dsimp [C]
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 7 by norm_num) d]
  refine ⟨C, hC, ?_⟩
  intro f B hB hf Ω _ μ _ ε ξ hε hξ X hX n hn
  classical
  let Y := ballFinset d (3 * (n : ℝ))
  let E : Site d → Set Ω := fun y => {ω |
    ¬ |dynkinMart (driftStepProb d ε ξ) (f n y) (X · ω) n| ≤
      A * (Real.sqrt (dynkinBracket (driftStepProb d ε ξ) (f n y) (f n y)
        (X · ω) n * Real.log n) + B n * Real.log n)}
  have hsub : {ω | ¬ ∀ y : Site d, euclidNorm y ≤ 3 * n →
      |dynkinMart (driftStepProb d ε ξ) (f n y) (X · ω) n| ≤
        C * (Real.sqrt (dynkinBracket (driftStepProb d ε ξ) (f n y) (f n y)
          (X · ω) n * Real.log n) + B n * Real.log n)} ⊆ ⋃ y ∈ Y, E y := by
    intro ω hbad
    simp only [Set.mem_setOf_eq, not_forall] at hbad
    obtain ⟨y, hy, hyn⟩ := hbad
    simp only [Set.mem_iUnion]
    refine ⟨y, mem_ballFinset_iff.mpr hy, ?_⟩
    intro hgood
    apply hyn
    exact hgood.trans (mul_le_mul_of_nonneg_right hAC (by
      have := Real.log_natCast_nonneg n
      have := (hB n hn).le
      positivity))
  have htail : ∀ y : Site d, μ (E y) ≤ ENNReal.ofReal (A * (n : ℝ) ^ (-(p + d))) := by
    intro y
    exact hF n hn n le_rfl hd μ ε ξ hε hξ X hX (f n y) (B n) (hB n hn) (hf n hn y)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  have hcard : (Y.card : ℝ) ≤ 7 ^ d * (n : ℝ) ^ d := by
    calc (Y.card : ℝ) ≤ (2 * (3 * (n : ℝ)) + 1) ^ d :=
        card_ballFinset_le d (by positivity)
      _ ≤ (7 * (n : ℝ)) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
      _ = 7 ^ d * (n : ℝ) ^ d := mul_pow _ _ d
  have hpower : (n : ℝ) ^ d * (n : ℝ) ^ (-(p + d)) = (n : ℝ) ^ (-p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn0]
    congr 1
    ring
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le Y E).trans ?_)
  calc ∑ y ∈ Y, μ (E y) ≤ ∑ _y ∈ Y, ENNReal.ofReal (A * (n : ℝ) ^ (-(p + d))) :=
        Finset.sum_le_sum fun y _ => htail y
    _ = ENNReal.ofReal ((Y.card : ℝ) * (A * (n : ℝ) ^ (-(p + d)))) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
      apply ENNReal.ofReal_le_ofReal
      calc (Y.card : ℝ) * (A * (n : ℝ) ^ (-(p + d)))
          ≤ (7 ^ d * (n : ℝ) ^ d) * (A * (n : ℝ) ^ (-(p + d))) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = (7 ^ d * A) * (n : ℝ) ^ (-p) := by rw [← hpower]; ring
        _ ≤ C * (n : ℝ) ^ (-p) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          dsimp [C]
          nlinarith


/-- The actual-bracket kernel Freedman estimate holds simultaneously at all targets
within distance `3n`, with constants uniform in the admissible drift field. -/
theorem exists_localMartingaleBound {d : ℕ} (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      0 ≤ ε → (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ LocalMartingaleBound ε ξ C (X · ω) n} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨A, hA, hfamily⟩ := exists_family_bound.{u} (by omega : 1 ≤ d) p hp
  obtain ⟨_, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts_latticeKernel hd
  obtain ⟨Cg, hgrad⟩ := hK.gradBound
  have hCg := CERW.Support.Law.cg_nonneg (by omega : 1 ≤ d) hgrad
  let B := Cg + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hstep : ∀ (_n : ℕ), 2 ≤ _n → ∀ y x e : Site d, e ∈ unitSteps d →
      |latticeKernel d (x + e - y) - latticeKernel d (x - y)| ≤ B := by
    intro _ _ y x e he
    rw [add_sub_right_comm]
    have h := hgrad (x - y) e he
    have hpow : (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [euclidNorm_nonneg (x - y)])
        (by have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
            linarith)
    exact h.trans ((mul_le_mul_of_nonneg_left hpow hCg).trans (by dsimp [B]; linarith))
  refine ⟨A * (B + 1), by positivity, ?_⟩
  intro ε ξ hε hξ Ω _ μ _ X hX n hn
  have htail := hfamily (fun _ y z => latticeKernel d (z - y)) (fun _ => B)
    (fun _ _ => hB) hstep μ ε ξ hε hξ X hX n hn
  refine (measure_mono ?_).trans (htail.trans (ENNReal.ofReal_le_ofReal ?_))
  · intro ω hbad hgood
    apply hbad
    intro y hy
    have h := hgood y hy
    have hs := Real.sqrt_nonneg (dynkinBracket (driftStepProb d ε ξ)
      (fun z => latticeKernel d (z - y)) (fun z => latticeKernel d (z - y))
      (X · ω) n * Real.log n)
    have hl := Real.log_natCast_nonneg n
    change |dynkinMart _ _ _ _| ≤ _ at h ⊢
    nlinarith [mul_nonneg (mul_nonneg hA.le hB.le) hs, mul_nonneg hA.le hl]
  · exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)

/-- The shifted-square Freedman constituent of `sec:norm-event`, simultaneously
for all targets in the prescribed lattice ball. -/
theorem exists_squareMartingaleBound {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (p : ℝ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ SquareMartingaleBound Ψ ε ξ C (X · ω) n} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨A, hA, hfamily⟩ := exists_family_bound.{u} (by omega : 1 ≤ d) p hp
  obtain ⟨B, hB, hstep⟩ := ShiftedSquare.exists_squareKernel_step_bound hd hΨ hε
  let gbar : ℕ → ℝ := fun n => if d = 2 then Real.log n else 1
  have hbar : ∀ n : ℕ, 2 ≤ n → 0 < gbar n := by
    intro n hn
    dsimp [gbar]
    split_ifs
    · exact Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    · exact zero_lt_one
  refine ⟨A * (B + 1), by positivity, ?_⟩
  intro ξ hξ Ω _ μ _ X hX n hn
  have htail := hfamily (fun n y => squareKernel Ψ ε n y) (fun n => B * gbar n)
    (fun n hn => mul_pos hB (hbar n hn)) hstep μ ε ξ hε.le hξ X hX n hn
  refine (measure_mono ?_).trans (htail.trans (ENNReal.ofReal_le_ofReal ?_))
  · intro ω hbad hgood
    apply hbad
    intro y hy
    have h := hgood y hy
    have hs := Real.sqrt_nonneg (dynkinBracket (driftStepProb d ε ξ)
      (squareKernel Ψ ε n y) (squareKernel Ψ ε n y) (X · ω) n * Real.log n)
    have hl := mul_nonneg (hbar n hn).le (Real.log_natCast_nonneg n)
    change |dynkinMart _ _ _ _| ≤ _ at h ⊢
    change |dynkinMart _ _ _ _| ≤
      A * (B + 1) * (Real.sqrt (dynkinBracket (driftStepProb d ε ξ)
        (squareKernel Ψ ε n y) (squareKernel Ψ ε n y) (X · ω) n * Real.log n) +
        gbar n * Real.log n)
    nlinarith [mul_nonneg (mul_nonneg hA.le hB.le) hs, mul_nonneg hA.le hl]
  · exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)

end CERW.LimitShapes.KernelEvents
