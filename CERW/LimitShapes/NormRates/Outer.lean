import CERW.LimitShapes.Event
import CERW.Support.Norm.ShapeRates

/-!
# Outer radius from distance crossing

The last step of Proposition `prop:norm-shape` uses the simultaneous distance
crossing estimate at the deterministic level equal to the predicted radius.
-/

open LatticeProb (Site)

namespace CERW.LimitShapes

open CERW.Support.Norm.ProjectionGeometry
open private CERW.Support.Norm.rateQ
  CERW.Support.Norm.RateInequalities.one_le_mul_rpow from CERW.Support.Norm.ShapeRates

/-- The global cone error bounds the exterior local time at the cone radius. -/
theorem exteriorLocalTime_le_cone_error {d : ℕ}
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ε r B : ℝ} {X : ℕ → Site d} {n : ℕ}
    (hB : 0 ≤ B)
    (hprofile : ∀ y : EuclideanSpace ℝ (Fin d),
      |cellLocalTime X n y - 2 * d * ε * max (r - Ψ y) 0| ≤ B) :
    (exteriorLocalTime Ψ X n r : ℝ) ≤ B := by
  classical
  unfold exteriorLocalTime
  apply le_trans (b := (⌊B⌋₊ : ℝ)) _ (Nat.floor_le hB)
  apply Nat.cast_le.mpr
  apply Finset.sup_le
  intro z hz
  have hzlevel := (Finset.mem_filter.mp hz).2
  have h := hprofile (toSpace z)
  rw [cellLocalTime_of_mem_cell _ _ (toSpace_mem_cell z),
    max_eq_right (sub_nonpos.mpr hzlevel), mul_zero, sub_zero,
    abs_of_nonneg (Nat.cast_nonneg _)] at h
  exact (Nat.le_floor_iff hB).mpr h

/-- Distance crossing at `a = r` turns a global cone estimate into an outer-radius bound. -/
theorem normMaxRadius_le_of_distance_crossing {d : ℕ}
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ε r B C : ℝ} (hr : 0 ≤ r) (hB : 0 ≤ B) (hC : 0 ≤ C)
    {X : ℕ → Site d} {n : ℕ} (hlog : 0 ≤ Real.log n)
    (hcross : DistanceCrossingBound Ψ C X n)
    (hprofile : ∀ y : EuclideanSpace ℝ (Fin d),
      |cellLocalTime X n y - 2 * d * ε * max (r - Ψ y) 0| ≤ B) :
    normMaxRadius Ψ X n - r ≤ normMax Ψ * C * (1 + B) * Real.log n := by
  have hΛ : 0 ≤ normMax Ψ := by
    apply Real.sSup_nonneg
    rintro _ ⟨v, -, rfl⟩
    exact (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 v
  have hne : ({v : EuclideanSpace ℝ (Fin d) | Ψ v ≤ r}).Nonempty :=
    ⟨0, by simpa only [Set.mem_setOf_eq,(CERW.Generic.Norm.map_zero_nonneg_neg hΨ).1] using hr⟩
  have hext := exteriorLocalTime_le_cone_error hB hprofile
  have hsites : ∀ j ≤ n,
      Ψ (toSpace (X j)) ≤ r + normMax Ψ * C * (1 + B) * Real.log n := by
    intro j hj
    obtain ⟨z, hz, hdist⟩ := (isClosed_sublevel hΨ r).exists_infDist_eq_dist hne
      (toSpace (X j))
    have hgeom := le_add_normMax_mul_dist hΨ (y := toSpace (X j)) hz
    rw [← dist_eq_norm, ← hdist] at hgeom
    have hc := hcross n le_rfl r hr j hj
    have hc' : Metric.infDist (toSpace (X j)) {v | Ψ v ≤ r} ≤
        C * (1 + B) * Real.log n := hc.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith :
          1 + (exteriorLocalTime Ψ X n r : ℝ) ≤ 1 + B) hC) hlog)
    have := mul_le_mul_of_nonneg_left hc' hΛ
    nlinarith
  have hmax : normMaxRadius Ψ X n ≤
      r + normMax Ψ * C * (1 + B) * Real.log n := by
    apply Finset.sup'_le
    intro j hj
    exact hsites j (by have := Finset.mem_range.mp hj; omega)
  linarith

/-- Absorbing the constant in the crossing bound gives the outer rate in
Proposition `prop:norm-shape`. -/
theorem norm_outer_rate_of_distance_crossing {d : ℕ}
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ε r C L : ℝ} (hr : 1 ≤ r) (hC : 0 ≤ C) (hL : 0 ≤ L)
    {X : ℕ → Site d} {n : ℕ} (hlog : 1 ≤ Real.log n) (hlogr : Real.log n ≤ r)
    (hcross : DistanceCrossingBound Ψ C X n)
    (hprofile : ∀ y : EuclideanSpace ℝ (Fin d),
      |cellLocalTime X n y - 2 * d * ε * max (r - Ψ y) 0| ≤
        L * (r * CERW.Support.Norm.rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1)))) :
    normMaxRadius Ψ X n - r ≤ normMax Ψ * C * (1 + L) *
      (r * CERW.Support.Norm.rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1)) *
        Real.log n) := by
  have hscale := CERW.Support.Norm.RateInequalities.one_le_mul_rpow d hr hlog hlogr
  have hB : 0 ≤ L *
      (r * CERW.Support.Norm.rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1))) := by
    positivity
  have h := normMaxRadius_le_of_distance_crossing hΨ (by linarith) hB hC
    (by linarith) hcross hprofile
  have hshift : 1 + L *
      (r * CERW.Support.Norm.rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1))) ≤
      (1 + L) *
        (r * CERW.Support.Norm.rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1))) := by
    nlinarith
  have hΛ : 0 ≤ normMax Ψ := by
    apply Real.sSup_nonneg
    rintro _ ⟨v, -, rfl⟩
    exact (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 v
  calc _ ≤ normMax Ψ * C * (1 + L *
      (r * CERW.Support.Norm.rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1)))) *
        Real.log n := h
    _ ≤ normMax Ψ * C * ((1 + L) *
        (r * CERW.Support.Norm.rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1)))) *
          Real.log n := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hshift (mul_nonneg hΛ hC)) (by linarith)
    _ = _ := by ring

end CERW.LimitShapes
