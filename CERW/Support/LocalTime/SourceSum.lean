import CERW.Support.LocalTime.ReplaceGradient
import CERW.Support.LocalTime.ReplaceCell
import CERW.Support.LocalTime.ReplaceDirection
import CERW.Support.Geometry.Bound
import CERW.Support.Occupation.CellIntegral

/-!
# The source sum is the potential up to a logarithm

The deterministic core of `eq:approx` and `eq:pointwise`: for a lattice target `y`, the source sum
`ε Σ_{x ∈ A_n} u_x · Db(x - y)` of `eq:dynkin` differs from `U_{D_n}(y)` by at most
`C ε log(R' + 2)`.
Three replacements do it: the gradient by the Newtonian field, the kernel value by its cell
integral, and the lattice direction by the continuous one. After them, the sum of cell integrals is
the integral over `D_n`.
-/

namespace CERW.Support.LocalTime

open MeasureTheory LatticeProb CERW CERW.Support.Law CERW.Generic.Kernel CERW.Support.Occupation

variable {d : ℕ}

/-- The embedding of lattice sites is additive. -/
private lemma toSpace_sub_local (x y : Site d) :
    toSpace (x - y) = toSpace x - toSpace y := by
  ext i
  simp [toSpace, Pi.sub_apply, Int.cast_sub]

/-- The Newtonian field is Borel measurable. -/
private lemma newtonField_measurable_local :
    Measurable (newtonField : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) := by
  have h1 : Measurable (fun v : EuclideanSpace ℝ (Fin d) => (‖v‖ ^ d)⁻¹) :=
    (measurable_norm.pow_const d).inv
  exact h1.smul measurable_id

/-- For fixed `w` and `z`, `v ↦ ⟪w, K(v - z)⟫` is measurable. -/
private lemma inner_newtonField_measurable_local (w z : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ w (newtonField (v - z))) := by
  have hcomp : Measurable (fun v : EuclideanSpace ℝ (Fin d) => newtonField (v - z)) :=
    newtonField_measurable_local.comp (measurable_id.sub measurable_const)
  exact continuous_inner.measurable.comp (measurable_const.prodMk hcomp)

/-- For `‖w‖ ≤ 1`, `v ↦ ⟪w, K(v - z)⟫` is integrable on a measurable set of finite volume. -/
private lemma integrableOn_inner_newtonField_of_norm_le (hd : 2 ≤ d)
    (w : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ ≤ 1)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤)
    (z : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => inner ℝ w (newtonField (v - z))) D volume := by
  have hbase : IntegrableOn (fun v => ‖v - z‖ ^ (1 - (d : ℝ))) D volume :=
    (integrableOn_and_setIntegral_le (d := d) (by omega : 1 ≤ d) hD hDfin z).1
  refine hbase.mono' (inner_newtonField_measurable_local w z).aestronglyMeasurable ?_
  filter_upwards with v
  calc ‖inner ℝ w (newtonField (v - z))‖
      ≤ ‖w‖ * ‖newtonField (v - z)‖ := norm_inner_le_norm _ _
    _ = ‖w‖ * ‖v - z‖ ^ (1 - (d : ℝ)) := by rw [norm_newtonField hd]
    _ ≤ 1 * ‖v - z‖ ^ (1 - (d : ℝ)) :=
        mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg (norm_nonneg _) _)
    _ = ‖v - z‖ ^ (1 - (d : ℝ)) := by rw [one_mul]

/-- The integrand `v ↦ ⟪u_v, K(v - z)⟫` is integrable on a measurable set of finite volume. -/
private lemma integrableOn_inner_unitDir_newtonField (hd : 2 ≤ d)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤)
    (z : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => inner ℝ (unitDir v) (newtonField (v - z))) D volume := by
  have h := CERW.Support.Geometry.integrableOn_potentialIntegrand (d := d)
    (by omega : 1 ≤ d) hD hDfin z
  refine h.congr ?_
  filter_upwards with v
  exact (inner_newtonField (unitDir v) (v - z)).symm

/-- The source sum of `eq:dynkin` differs from the potential by `O(ε log(R' + 2))`. -/
theorem exists_abs_source_sum_sub_potential_le (hd : 2 ≤ d) {b : Site d → ℝ} {Ca R Cg : ℝ}
    (hR : 1 ≤ R)
    (hgradA : ∀ x, R ≤ euclidNorm x →
      ‖centralDiff b x - (2 / unitBallVolume d / euclidNorm x ^ d) • toSpace x‖ ≤
        Ca * euclidNorm x ^ (-(d : ℝ)))
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ (X : ℕ → Site d) (n : ℕ) (y : Site d) (R' : ℝ),
      1 ≤ R' → euclidNorm y ≤ 2 * R' →
      (∀ x ∈ departureRange X n, euclidNorm (x - y) ≤ R' ∧ cell x ⊆ Metric.ball 0 R') →
        |ε * ∑ x ∈ departureRange X n, inner ℝ (unitDir (toSpace x)) (centralDiff b (x - y)) -
            potential d ε (cellSet X n) (toSpace y)| ≤ C * ε * Real.log (R' + 2) := by
  obtain ⟨Ca, hCa_nonneg, hCa⟩ :=
    exists_sum_norm_centralDiff_sub_newtonField_le (d := d) hd hR hgradA hgrad
  obtain ⟨Cb, hCb_nonneg, hCb⟩ := exists_sum_abs_newtonField_sub_setIntegral_le (d := d) hd
  obtain ⟨Cc, hCc_nonneg, hCc⟩ := exists_sum_abs_setIntegral_unitDir_sub_le (d := d) hd
  refine ⟨Ca + (2 / unitBallVolume d) * (Cb + Cc), ?_, ?_⟩
  · have hcoef : 0 ≤ 2 / unitBallVolume d :=
      le_of_lt (div_pos (by norm_num) (unitBallVolume_pos d))
    exact add_nonneg hCa_nonneg (mul_nonneg hcoef (add_nonneg hCb_nonneg hCc_nonneg))
  · intro ε hε X n y R' hR' hy hcell
    set S0 : ℝ := ∑ x ∈ departureRange X n,
      inner ℝ (unitDir (toSpace x)) (centralDiff b (x - y)) with hS0
    set S1 : ℝ := ∑ x ∈ departureRange X n,
      inner ℝ (unitDir (toSpace x)) (newtonField (toSpace x - toSpace y)) with hS1
    set S2 : ℝ := ∑ x ∈ departureRange X n,
      ∫ v in cell x, inner ℝ (unitDir (toSpace x)) (newtonField (v - toSpace y)) with hS2
    set S3 : ℝ := ∑ x ∈ departureRange X n,
      ∫ v in cell x, inner ℝ (unitDir v) (newtonField (v - toSpace y)) with hS3
    have hfac : 0 ≤ 2 / unitBallVolume d :=
      le_of_lt (div_pos (by norm_num) (unitBallVolume_pos d))
    have h1 : |S0 - (2 / unitBallVolume d) * S1| ≤ Ca * Real.log (R' + 2) := by
      have hsum := hCa (departureRange X n) y R' hR' (fun x hx => (hcell x hx).1)
      have hrew : S0 - (2 / unitBallVolume d) * S1 =
          ∑ x ∈ departureRange X n, inner ℝ (unitDir (toSpace x))
            (centralDiff b (x - y) -
              (2 / unitBallVolume d) • newtonField (toSpace x - toSpace y)) := by
        rw [hS0, hS1, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        rw [inner_sub_right, inner_smul_right]
      rw [hrew]
      calc |∑ x ∈ departureRange X n, inner ℝ (unitDir (toSpace x))
              (centralDiff b (x - y) -
                (2 / unitBallVolume d) • newtonField (toSpace x - toSpace y))|
          ≤ ∑ x ∈ departureRange X n, ‖inner ℝ (unitDir (toSpace x))
              (centralDiff b (x - y) -
                (2 / unitBallVolume d) • newtonField (toSpace x - toSpace y))‖ :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ x ∈ departureRange X n,
              ‖centralDiff b (x - y) -
                (2 / unitBallVolume d) • newtonField (toSpace x - toSpace y)‖ := by
            apply Finset.sum_le_sum
            intro x hx
            calc ‖inner ℝ (unitDir (toSpace x))
                    (centralDiff b (x - y) -
                      (2 / unitBallVolume d) • newtonField (toSpace x - toSpace y))‖
                ≤ ‖unitDir (toSpace x)‖ *
                    ‖centralDiff b (x - y) -
                      (2 / unitBallVolume d) • newtonField (toSpace x - toSpace y)‖ :=
                  norm_inner_le_norm _ _
              _ ≤ 1 * ‖centralDiff b (x - y) -
                      (2 / unitBallVolume d) • newtonField (toSpace x - toSpace y)‖ :=
                  mul_le_mul_of_nonneg_right (norm_unitDir_le _) (norm_nonneg _)
              _ = ‖centralDiff b (x - y) -
                      (2 / unitBallVolume d) • newtonField (toSpace x - toSpace y)‖ := by
                  rw [one_mul]
        _ = ∑ x ∈ departureRange X n,
              ‖centralDiff b (x - y) -
                (2 / unitBallVolume d) • newtonField (toSpace (x - y))‖ := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [← toSpace_sub_local x y]
        _ ≤ Ca * Real.log (R' + 2) := hsum
    have h2 : |(2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2| ≤
        (2 / unitBallVolume d) * Cb * Real.log (R' + 2) := by
      have hsum := hCb (departureRange X n) (fun x => unitDir (toSpace x)) y R' hR'
        (fun x => norm_unitDir_le (toSpace x)) (fun x hx => (hcell x hx).1)
      have hrew : S1 - S2 =
          ∑ x ∈ departureRange X n,
            (inner ℝ (unitDir (toSpace x)) (newtonField (toSpace x - toSpace y)) -
              ∫ v in cell x, inner ℝ (unitDir (toSpace x))
                (newtonField (v - toSpace y))) := by
        rw [hS1, hS2, ← Finset.sum_sub_distrib]
      have htri : |S1 - S2| ≤
          ∑ x ∈ departureRange X n,
            |inner ℝ (unitDir (toSpace x)) (newtonField (toSpace x - toSpace y)) -
              ∫ v in cell x, inner ℝ (unitDir (toSpace x))
                (newtonField (v - toSpace y))| := by
        rw [hrew]
        exact Finset.abs_sum_le_sum_abs _ _
      calc |(2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2|
          = (2 / unitBallVolume d) * |S1 - S2| := by
            rw [← mul_sub, abs_mul, abs_of_nonneg hfac]
        _ ≤ (2 / unitBallVolume d) *
              (∑ x ∈ departureRange X n,
                |inner ℝ (unitDir (toSpace x)) (newtonField (toSpace x - toSpace y)) -
                  ∫ v in cell x, inner ℝ (unitDir (toSpace x))
                    (newtonField (v - toSpace y))|) :=
            mul_le_mul_of_nonneg_left htri hfac
        _ ≤ (2 / unitBallVolume d) * (Cb * Real.log (R' + 2)) :=
            mul_le_mul_of_nonneg_left hsum hfac
        _ = (2 / unitBallVolume d) * Cb * Real.log (R' + 2) := by ring
    have h3 : |(2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3| ≤
        (2 / unitBallVolume d) * Cc * Real.log (R' + 2) := by
      have hsum := hCc (departureRange X n) (toSpace y) R' hR' (by rwa [norm_toSpace])
        (fun x hx => (hcell x hx).2)
      have hrew : S2 - S3 =
          ∑ x ∈ departureRange X n,
            ∫ v in cell x,
              inner ℝ (unitDir (toSpace x) - unitDir v) (newtonField (v - toSpace y)) := by
        rw [hS2, hS3, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        have hcellmeas : MeasurableSet (cell x) := measurableSet_cell x
        have hcellfin : volume (cell x) ≠ ⊤ := by
          rw [volume_cell]; exact ENNReal.one_ne_top
        have hleft : IntegrableOn
            (fun v => inner ℝ (unitDir (toSpace x)) (newtonField (v - toSpace y)))
            (cell x) volume :=
          integrableOn_inner_newtonField_of_norm_le hd (unitDir (toSpace x))
            (norm_unitDir_le _) hcellmeas hcellfin (toSpace y)
        have hright : IntegrableOn
            (fun v => inner ℝ (unitDir v) (newtonField (v - toSpace y)))
            (cell x) volume :=
          integrableOn_inner_unitDir_newtonField hd hcellmeas hcellfin (toSpace y)
        rw [← integral_sub hleft hright]
        exact setIntegral_congr_fun hcellmeas (fun v _ => by rw [inner_sub_left])
      have htri : |S2 - S3| ≤
          ∑ x ∈ departureRange X n,
            |∫ v in cell x,
              inner ℝ (unitDir (toSpace x) - unitDir v)
                (newtonField (v - toSpace y))| := by
        rw [hrew]
        exact Finset.abs_sum_le_sum_abs _ _
      calc |(2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3|
          = (2 / unitBallVolume d) * |S2 - S3| := by
            rw [← mul_sub, abs_mul, abs_of_nonneg hfac]
        _ ≤ (2 / unitBallVolume d) *
              (∑ x ∈ departureRange X n,
                |∫ v in cell x,
                  inner ℝ (unitDir (toSpace x) - unitDir v)
                    (newtonField (v - toSpace y))|) :=
            mul_le_mul_of_nonneg_left htri hfac
        _ ≤ (2 / unitBallVolume d) * (Cc * Real.log (R' + 2)) :=
            mul_le_mul_of_nonneg_left hsum hfac
        _ = (2 / unitBallVolume d) * Cc * Real.log (R' + 2) := by ring
    have hmain : |S0 - (2 / unitBallVolume d) * S3| ≤
        (Ca + (2 / unitBallVolume d) * (Cb + Cc)) * Real.log (R' + 2) := by
      have htri : |S0 - (2 / unitBallVolume d) * S3| ≤
          |S0 - (2 / unitBallVolume d) * S1| +
            |(2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2| +
              |(2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3| := by
        have heq : S0 - (2 / unitBallVolume d) * S3 =
            (S0 - (2 / unitBallVolume d) * S1) +
              ((2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2) +
                ((2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3) := by ring
        rw [heq]
        calc |(S0 - (2 / unitBallVolume d) * S1) +
                ((2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2) +
                  ((2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3)|
            ≤ |(S0 - (2 / unitBallVolume d) * S1) +
                  ((2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2)| +
                |(2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3| :=
              abs_add_le _ _
          _ ≤ (|S0 - (2 / unitBallVolume d) * S1| +
                  |(2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2|) +
                |(2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3| :=
              add_le_add (abs_add_le _ _) le_rfl
          _ = |S0 - (2 / unitBallVolume d) * S1| +
                |(2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2| +
                  |(2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3| := by ring
      calc |S0 - (2 / unitBallVolume d) * S3|
          ≤ |S0 - (2 / unitBallVolume d) * S1| +
              |(2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2| +
                |(2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3| := htri
        _ ≤ Ca * Real.log (R' + 2) +
              (2 / unitBallVolume d) * Cb * Real.log (R' + 2) +
                (2 / unitBallVolume d) * Cc * Real.log (R' + 2) :=
            add_le_add (add_le_add h1 h2) h3
        _ = (Ca + (2 / unitBallVolume d) * (Cb + Cc)) * Real.log (R' + 2) := by ring
    have hpot : potential d ε (cellSet X n) (toSpace y) =
        ε * ((2 / unitBallVolume d) * S3) := by
      have hD3 : ∫ v in cellSet X n, inner ℝ (unitDir v) (newtonField (v - toSpace y))
          = S3 := by
        rw [hS3, cellSet]
        exact integral_biUnion_finset (departureRange X n) (fun x _ => measurableSet_cell x)
          (fun x _ y _ hxy => cell_disjoint hxy)
          (fun x _ => integrableOn_inner_unitDir_newtonField hd (measurableSet_cell x)
            (by rw [volume_cell]; exact ENNReal.one_ne_top) (toSpace y))
      have hcongr : ∫ v in cellSet X n,
            inner ℝ (unitDir v) (v - toSpace y) / ‖v - toSpace y‖ ^ d
          = ∫ v in cellSet X n,
            inner ℝ (unitDir v) (newtonField (v - toSpace y)) := by
        exact setIntegral_congr_fun (measurableSet_cellSet X n)
          (fun v _ => (inner_newtonField (unitDir v) (v - toSpace y)).symm)
      rw [potential, hcongr, hD3]
      ring
    calc |ε * S0 - potential d ε (cellSet X n) (toSpace y)|
        = |ε * S0 - ε * ((2 / unitBallVolume d) * S3)| := by rw [hpot]
      _ = ε * |S0 - (2 / unitBallVolume d) * S3| := by
          rw [← mul_sub, abs_mul, abs_of_nonneg hε]
      _ ≤ ε * ((Ca + (2 / unitBallVolume d) * (Cb + Cc)) * Real.log (R' + 2)) :=
          mul_le_mul_of_nonneg_left hmain hε
      _ = (Ca + (2 / unitBallVolume d) * (Cb + Cc)) * ε * Real.log (R' + 2) := by ring

end CERW.Support.LocalTime
