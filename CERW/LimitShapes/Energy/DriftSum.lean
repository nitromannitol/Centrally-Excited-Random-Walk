module

public import CERW.Generic.Lattice.Packing
public import CERW.Generic.Lattice.Centered
public import CERW.Support.LocalTime.LatticeKernelFacts

@[expose] public section

/-!
# Remote tail of the shifted-square drift envelope

The planar envelope in `lem:contact` has a uniformly controlled remote tail,
even when the finite set is not contained in a ball about the target.
-/

namespace CERW.LimitShapes.Energy

open CERW LatticeProb

/-- Beyond the centering radius, the planar envelope in `lem:contact` is at most
the reciprocal radius. -/
private theorem planar_envelope_le_inv {R u : ℝ} (hR : 0 < R) (hu : R ≤ u) :
    u⁻¹ * (1 + |Real.log (u / R)|) ≤ R⁻¹ := by
  have hu0 : 0 < u := lt_of_lt_of_le hR hu
  have hratio : 1 ≤ u / R := (le_div_iff₀ hR).2 (by simpa using hu)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hu0 hR)
  rw [abs_of_nonneg (Real.log_nonneg hratio)]
  calc
    u⁻¹ * (1 + Real.log (u / R)) ≤ u⁻¹ * (u / R) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hu0.le)
    _ = R⁻¹ := by field_simp

/-- A cardinality bound controls the entire remote planar tail in `lem:contact`;
no upper bound on the distances from the target is required. -/
private theorem sum_planar_envelope_remote_le {A R : ℝ} (hR : 0 < R)
    (S : Finset (Site 2)) (hcard : (S.card : ℝ) ≤ A * R ^ 2) (y : Site 2)
    (hremote : ∀ x ∈ S, R ≤ 1 + euclidNorm (x - y)) :
    ∑ x ∈ S, (1 + euclidNorm (x - y))⁻¹ *
      (1 + |Real.log ((1 + euclidNorm (x - y)) / R)|) ≤ A * R := by
  calc
    ∑ x ∈ S, (1 + euclidNorm (x - y))⁻¹ *
        (1 + |Real.log ((1 + euclidNorm (x - y)) / R)|)
        ≤ ∑ _x ∈ S, R⁻¹ :=
      Finset.sum_le_sum fun x hx => planar_envelope_le_inv hR (hremote x hx)
    _ = (S.card : ℝ) * R⁻¹ := by simp
    _ ≤ (A * R ^ 2) * R⁻¹ :=
      mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr hR.le)
    _ = A * R := by field_simp

end CERW.LimitShapes.Energy
