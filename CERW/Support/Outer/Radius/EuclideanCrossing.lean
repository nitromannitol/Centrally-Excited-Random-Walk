module

public import CERW.Support.Outer.Radius.PlanarHarmonicPotential

@[expose] public section

/-!
# Euclidean Crossing

The norm crossing estimate specializes to the Euclidean radial drift. Its bound converts small
exterior local times into control of the outer radius.
The retained labels `lem:outer-crossing`
refer to the earlier source `paper/limit-shapes.tex`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- The largest value of the Euclidean norm on the unit sphere is one. -/
lemma cr_normMax_euclid (hd : 1 ≤ d) :
    normMax (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) = 1 := by
  have hmem : coordVec (⟨0, by omega⟩ : Fin d) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by
    rw [mem_sphere_zero_iff_norm]
    simp [coordVec, PiLp.norm_single]
  have himg : (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ''
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 = {1} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨_, hmem, ?_⟩, ?_⟩
    · exact mem_sphere_zero_iff_norm.mp hmem
    · rintro t ⟨v, hv, rfl⟩
      exact mem_sphere_zero_iff_norm.mp hv
  rw [normMax, himg, csSup_singleton]

/-- For `n ≥ 2` one has `log (n + 2) ≤ 2 log n`. -/
lemma cr_log_add_two_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  calc Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.log_le_log (by linarith) h1
    _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num

/-- The vector increment bound with `log (n + 2)` implies the one with `log n` and the
constant doubled. -/
lemma cr_sqrt_le {a l l' C : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hl : 0 ≤ l)
    (hll : l' ≤ 2 * l) :
    C * Real.sqrt (a * l') ≤ 2 * C * Real.sqrt (a * l) := by
  have hsq : Real.sqrt (a * l') ≤ 2 * Real.sqrt (a * l) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h0 : Real.sqrt (a * l) ^ 2 = a * l := Real.sq_sqrt (mul_nonneg ha hl)
    calc a * l' ≤ a * (2 * l) := mul_le_mul_of_nonneg_left hll ha
      _ ≤ a * (4 * l) := mul_le_mul_of_nonneg_left (by linarith) ha
      _ = (2 * Real.sqrt (a * l)) ^ 2 := by rw [mul_pow, h0]; ring
  calc C * Real.sqrt (a * l') ≤ C * (2 * Real.sqrt (a * l)) :=
        mul_le_mul_of_nonneg_left hsq hC
    _ = 2 * C * Real.sqrt (a * l) := by ring

/-- The direction of a nonzero vector has norm one. -/
lemma cr_norm_unitDir {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    ‖unitDir v‖ = 1 := by
  rw [unitDir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

/-- The direction of a nonzero vector `v` has inner product `‖v‖` with `v`. -/
lemma cr_inner_unitDir_self {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    inner ℝ (unitDir v) v = ‖v‖ := by
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [unitDir, real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp

/-- The inner product of `q` with the direction of `y` is `⟪q, y⟫ / ‖y‖`. -/
lemma cr_inner_unitDir_right (q y : EuclideanSpace ℝ (Fin d)) :
    inner ℝ q (unitDir y) = ‖y‖⁻¹ * inner ℝ q y := by
  rw [unitDir, real_inner_smul_right]

/-- `eq:euclid-crossing` from `lem:outer-crossing`. -/
theorem euclid_crossing (hcross : outer_crossing) (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) (C₀ C₁ : ℝ) (hC₁ : 0 < C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y : ℕ → Site d) (n : ℕ), 2 ≤ n → PathFacts d ε C₀ C₁ Y n →
      LinOK d ε C₁ Y n → CrossOK d C Y n := by
  obtain ⟨hΨ, hsub, hξ0, hell⟩ := CERW.Support.Main.euclidean_norm_hypotheses (d := d) hεd
  have hΛ := cr_normMax_euclid (d := d) (by omega)
  obtain ⟨C, hC, hmain⟩ := hcross hd (fun v => ‖v‖) hΨ ε hε hell (1 / 2) (by norm_num)
    (2 * C₁) (by positivity)
  refine ⟨2 * C, by positivity, ?_⟩
  intro Y n hn hY hlin b hb
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hO : (0 : ℝ) ≤ (outerMax Y n b : ℝ) := Nat.cast_nonneg _
  by_cases hRb : maxRadius Y n ≤ b
  · have h0 : 0 ≤ 2 * C * (1 + (outerMax Y n b : ℝ)) * Real.log n := by positivity
    linarith
  have hRb' : b < maxRadius Y n := not_le.mp hRb
  obtain ⟨j₀, hj₀mem, hj₀⟩ := Finset.exists_mem_eq_sup'
    (⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩ : (Finset.range (n + 1)).Nonempty)
    (fun j => euclidNorm (Y j))
  have hj₀n : j₀ ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₀mem)
  have hj₀' : maxRadius Y n = euclidNorm (Y j₀) := hj₀
  have hRpos : 0 < maxRadius Y n := lt_of_le_of_lt hb hRb'
  have hy0 : toSpace (Y j₀) ≠ 0 := by
    intro h
    have h1 : euclidNorm (Y j₀) = 0 := by rw [← norm_toSpace, h, norm_zero]
    linarith
  set q : EuclideanSpace ℝ (Fin d) := unitDir (toSpace (Y j₀)) with hqdef
  have hqn : ‖q‖ = 1 := cr_norm_unitDir hy0
  have hT : inner ℝ q (toSpace (Y j₀)) = maxRadius Y n := by
    rw [hqdef, cr_inner_unitDir_self hy0, norm_toSpace, hj₀']
  have hinner_le : ∀ z : Site d, inner ℝ q (toSpace z) ≤ euclidNorm z := by
    intro z
    calc inner ℝ q (toSpace z) ≤ ‖q‖ * ‖toSpace z‖ := real_inner_le_norm _ _
      _ = euclidNorm z := by rw [hqn, one_mul, norm_toSpace]
  have hq : ‖q‖ ≤ normMax (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) := by
    rw [hΛ, hqn]
  have key := hmain (fun z => unitDir (toSpace z)) hsub hξ0 n hn q hq Y hY.start hY.step
  rw [hΛ] at key
  simp only [mul_one] at key
  have hvecC : ∀ s t : ℕ, s < t → t ≤ n →
      ‖compPath d ε Y t - compPath d ε Y s‖ ≤
        2 * C₁ * Real.sqrt (((t : ℝ) - s) * Real.log n) := by
    intro s t hst htn
    have hst' : (s : ℝ) < t := by exact_mod_cast hst
    exact (hY.vec s t hst htn).trans
      (cr_sqrt_le hC₁.le (by linarith) hlog (cr_log_add_two_le hn))
  have hmartC : ∀ k : ℕ, k ≤ n →
      |dynkinMart (driftStepProb d ε (fun z => unitDir (toSpace z)))
          (fun z => max (inner ℝ q (toSpace z) - k) 0) Y n|
        ≤ 2 * C₁ * (Real.sqrt (Real.log n *
              ∑ z ∈ (departureRange Y n).filter
                (fun z => (k : ℝ) - 1 < inner ℝ q (toSpace z)),
              (localTime Y n z : ℝ)) + Real.log n) := by
    intro k hk
    have hs : euclidNorm (Y j₀) ≤ n :=
      (CERW.Support.Occupation.euclidNorm_le_of_steps Y hY.start hY.step j₀).trans
        (by exact_mod_cast hj₀n)
    exact hlin.mono (by linarith : C₁ ≤ 2 * C₁) (Y j₀) hs k hk
  have hmax : ∀ j ≤ n, inner ℝ q (toSpace (Y j)) ≤ inner ℝ q (toSpace (Y j₀)) := by
    intro j hj
    rw [hT]
    exact (hinner_le (Y j)).trans (hj₀' ▸ euclidNorm_le_maxRadius Y hj)
  have hdrift : ∀ j ≤ n, inner ℝ q (toSpace (Y j₀)) - maxRadius Y n / 2 <
      inner ℝ q (toSpace (Y j)) → (1 / 2 : ℝ) ≤ inner ℝ q (unitDir (toSpace (Y j))) := by
    intro j hj hlt
    rw [hT] at hlt
    have hpos : maxRadius Y n / 2 < inner ℝ q (toSpace (Y j)) := by linarith
    have hyj : toSpace (Y j) ≠ 0 := by
      intro h
      rw [h, inner_zero_right] at hpos
      linarith
    have hnyj : 0 < ‖toSpace (Y j)‖ := norm_pos_iff.mpr hyj
    have hnle : ‖toSpace (Y j)‖ ≤ maxRadius Y n := by
      rw [norm_toSpace]
      exact euclidNorm_le_maxRadius Y hj
    rw [cr_inner_unitDir_right, ← div_eq_inv_mul, le_div_iff₀ hnyj]
    linarith
  have fin : inner ℝ q (toSpace (Y j₀)) ≤ max (inner ℝ q (toSpace (Y j₀)) - maxRadius Y n / 2) b +
      C * (1 + ((((departureRange Y n).filter
        (fun z => b ≤ inner ℝ q (toSpace z))).sup (localTime Y n) : ℕ) : ℝ)) * Real.log n :=
    key hvecC hmartC j₀ hj₀n hmax (maxRadius Y n / 2) (by positivity) hdrift b hb
  rw [hT] at fin
  have hsup : ((departureRange Y n).filter
      (fun z => b ≤ inner ℝ q (toSpace z))).sup (localTime Y n) ≤ outerMax Y n b := by
    refine Finset.sup_mono ?_
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2.trans (hinner_le z)⟩
  have hsup' : ((((departureRange Y n).filter
      (fun z => b ≤ inner ℝ q (toSpace z))).sup (localTime Y n) : ℕ) : ℝ) ≤
        (outerMax Y n b : ℝ) := by exact_mod_cast hsup
  have hX : C * (1 + ((((departureRange Y n).filter
      (fun z => b ≤ inner ℝ q (toSpace z))).sup (localTime Y n) : ℕ) : ℝ)) * Real.log n ≤
        C * (1 + (outerMax Y n b : ℝ)) * Real.log n :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC.le) hlog
  have hX0 : 0 ≤ C * (1 + (outerMax Y n b : ℝ)) * Real.log n := by positivity
  rcases le_total (maxRadius Y n - maxRadius Y n / 2) b with h | h
  · rw [max_eq_right h] at fin
    linarith
  · rw [max_eq_left h] at fin
    linarith
/-! ### The linear martingales -/

end CERW.Support.Outer.Radius
