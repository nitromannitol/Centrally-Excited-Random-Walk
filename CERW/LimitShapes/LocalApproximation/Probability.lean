module

public import CERW.LimitShapes.LocalApproximation.Assembly
public import CERW.LimitShapes.KernelEvents

@[expose] public section

/-!
# Direct local-time approximation

Lemma `lem:local` follows from the final-time Dynkin decomposition, the actual-bracket
Freedman event, and the cell modulus.
-/

universe u

open MeasureTheory Filter LatticeProb CERW CERW.Support.Law CERW.Support.Drift

/-- The local approximation of Lemma `lem:local`, using the final-time Dynkin martingale. -/
theorem CERW.LimitShapes.local_time_potential_from_dynkin {d : ℕ} (hd : 2 ≤ d) :
    ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
    ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
            |CERW.cellLocalTime (X · ω) n y
                - CERW.normPotential d ε Ψ (CERW.cellSet (X · ω) n) y| ≤
              C * Real.log n + C *
                (if d = 2 then Real.sqrt (CERW.maxLocalTime (X · ω) n) * Real.log n
                  else Real.sqrt (CERW.maxLocalTime (X · ω) n * Real.log n))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))
:= by
  intro Ψ hΨ ε hε hell p hp
  obtain ⟨A, hA, ha⟩ :=
    CERW.LimitShapes.KernelEvents.exists_localMartingaleBound.{u} hd p hp
  obtain ⟨K, hK, hk⟩ :=
    CERW.LimitShapes.LocalApproximationProof.exists_path_approximation hd hΨ hε hA.le hell
  let N : ℕ := ⌈Real.sqrt d⌉₊ + 2
  let C : ℝ := K + A + (N : ℝ) ^ p
  have hpow : 0 ≤ (N : ℝ) ^ p := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hC : 0 < C := by dsimp [C]; positivity
  have hKC : K ≤ C := by dsimp [C]; linarith
  have hAC : A ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  have hξ' : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ) :=
    CERW.Support.Norm.ContactAssembly.drift_coord_le hΨ hε hell hξ hξ0
  by_cases hN : N ≤ n
  · have hsq : Real.sqrt d ≤ n := by
      have hceil := Nat.le_ceil (Real.sqrt (d : ℝ))
      have hbound : ((⌈Real.sqrt (d : ℝ)⌉₊ : ℕ) : ℝ) ≤ n := by
        exact_mod_cast (show ⌈Real.sqrt (d : ℝ)⌉₊ ≤ n by dsimp [N] at hN; omega)
      exact hceil.trans hbound
    have hnull : μ {ω | ¬ (X 0 ω = 0 ∧ ∀ j, euclidNorm (X j ω) ≤ j)} = 0 := by
      refine ae_iff.mp ?_
      filter_upwards [ae_iff.mpr hX.start,
        ae_euclidNorm_le_drift (by omega : 1 ≤ d) hε.le hξ' hX] with ω h0 hx
      exact ⟨h0, hx⟩
    refine measure_le_of_subset_union (fun ω hbad => ?_)
      (ha ε ξ hε.le hξ' μ X hX n hn) hnull
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAC
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
    by_contra hout
    rw [Set.mem_union, not_or] at hout
    obtain ⟨hm, hpath⟩ := hout
    simp only [Set.mem_setOf_eq, not_not] at hm hpath
    have hloc := hk ξ hξ hξ0 (X · ω) n hn hsq hpath.1 hpath.2 hm
    apply hbad
    intro y hy
    refine (hloc y hy).trans (add_le_add
      (mul_le_mul_of_nonneg_right hKC (Real.log_natCast_nonneg n)) ?_)
    apply mul_le_mul_of_nonneg_right hKC
    split_ifs <;> positivity
  · exact (prob_le_one).trans (ENNReal.one_le_ofReal.mpr
      (one_le_mul_rpow_neg hp (by omega) (not_le.mp hN).le (by dsimp [C]; linarith)))
