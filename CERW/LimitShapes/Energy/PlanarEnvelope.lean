module

public import CERW.LimitShapes.Energy.PlanarPacking
public import CERW.LimitShapes.Energy.DriftSum

@[expose] public section

/-!
# Planar logarithmic envelopes near the pole

The shifted logarithmic envelope in `lem:contact` has linear total mass on a planar
lattice ball, and on every set with quadratic cardinality growth.
-/

namespace CERW.LimitShapes.Energy

open CERW LatticeProb
open private sum_planar_envelope_remote_le from CERW.LimitShapes.Energy.DriftSum

/-- A square root dominates the logarithmic enhancement inside the centering radius. -/
private lemma planar_envelope_le_fractional {u R : ℝ} (hu : 0 < u) (huR : u ≤ R) :
    u⁻¹ * (1 + |Real.log (u / R)|) ≤
      3 * Real.sqrt R * (u * Real.sqrt u)⁻¹ := by
  have hR : 0 < R := hu.trans_le huR
  have hratio : 1 ≤ R / u := (le_div_iff₀ hu).2 (by simpa using huR)
  have hs : 1 ≤ Real.sqrt (R / u) := by
    simpa using Real.sqrt_le_sqrt hratio
  have hlog := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (div_pos hR hu))
  rw [Real.log_sqrt (div_nonneg hR.le hu.le)] at hlog
  have habs : |Real.log (u / R)| = Real.log (R / u) := by
    rw [abs_of_nonpos (Real.log_nonpos (div_nonneg hu.le hR.le)
      ((div_le_one hR).2 huR)), Real.log_div (ne_of_gt hu) (ne_of_gt hR),
      Real.log_div (ne_of_gt hR) (ne_of_gt hu)]
    ring
  rw [habs]
  calc
    u⁻¹ * (1 + Real.log (R / u)) ≤ u⁻¹ * (3 * Real.sqrt (R / u)) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 3 * Real.sqrt R * (u * Real.sqrt u)⁻¹ := by
      rw [Real.sqrt_div hR.le]
      field_simp

/-- The near-pole planar envelope in `lem:contact` has total mass at most linear in `R`. -/
theorem exists_sum_planar_envelope_near_le :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R →
      ∀ (S : Finset (Site 2)) (y : Site 2),
        (∀ x ∈ S, 1 + euclidNorm (x - y) ≤ R) →
        ∑ x ∈ S, (1 + euclidNorm (x - y))⁻¹ *
          (1 + |Real.log ((1 + euclidNorm (x - y)) / R)|) ≤ C * R := by
  refine ⟨102, by norm_num, ?_⟩
  intro R hR S y hS
  have hfrac := sum_planar_fractional_le S y R (by linarith)
    (fun x hx => by have := hS x hx; linarith)
  have hs : Real.sqrt R * Real.sqrt (R + 1) ≤ 2 * R := by
    have ha := Real.sq_sqrt (by linarith : 0 ≤ R)
    have hb := Real.sq_sqrt (by linarith : 0 ≤ R + 1)
    have hle : Real.sqrt (R + 1) ≤ 2 * Real.sqrt R := by
      nlinarith [Real.sqrt_nonneg R, Real.sqrt_nonneg (R + 1)]
    nlinarith [Real.sqrt_nonneg R]
  calc
    _ ≤ ∑ x ∈ S, 3 * Real.sqrt R *
        ((1 + euclidNorm (x - y)) * Real.sqrt (1 + euclidNorm (x - y)))⁻¹ :=
      Finset.sum_le_sum fun x hx =>
        planar_envelope_le_fractional
          (by have := euclidNorm_nonneg (x - y); positivity) (hS x hx)
    _ = 3 * Real.sqrt R * ∑ x ∈ S,
        ((1 + euclidNorm (x - y)) * Real.sqrt (1 + euclidNorm (x - y)))⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ 3 * Real.sqrt R * (17 * Real.sqrt (R + 1)) :=
      mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ ≤ 102 * R := by nlinarith

/-- Quadratic cardinality growth suffices for the planar envelope bound of `lem:contact`. -/
theorem exists_sum_planar_envelope_le (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R →
      ∀ (S : Finset (Site 2)) (y : Site 2), (S.card : ℝ) ≤ A * R ^ 2 →
        ∑ x ∈ S, (1 + euclidNorm (x - y))⁻¹ *
          (1 + |Real.log ((1 + euclidNorm (x - y)) / R)|) ≤ C * R := by
  classical
  obtain ⟨C, hC, hnear⟩ := exists_sum_planar_envelope_near_le
  refine ⟨C + A, by positivity, ?_⟩
  intro R hR S y hcard
  let T := S.filter (fun x => 1 + euclidNorm (x - y) ≤ R)
  have hT : ∀ x ∈ T, 1 + euclidNorm (x - y) ≤ R := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hremote : ∀ x ∈ S \ T, R ≤ 1 + euclidNorm (x - y) := by
    intro x hx
    have h := Finset.mem_sdiff.mp hx
    have : ¬ 1 + euclidNorm (x - y) ≤ R := by
      intro hle
      exact h.2 (Finset.mem_filter.mpr ⟨h.1, hle⟩)
    exact (lt_of_not_ge this).le
  have hcard' : ((S \ T).card : ℝ) ≤ A * R ^ 2 :=
    (Nat.cast_le.mpr (Finset.card_le_card Finset.sdiff_subset)).trans hcard
  have hn := hnear R hR T y hT
  have hf := sum_planar_envelope_remote_le (by linarith) (S \ T) hcard' y hremote
  have hsplit := Finset.sum_sdiff (f := fun x : Site 2 =>
    (1 + euclidNorm (x - y))⁻¹ * (1 + |Real.log ((1 + euclidNorm (x - y)) / R)|))
    (show T ⊆ S from Finset.filter_subset _ _)
  linarith

end CERW.LimitShapes.Energy
