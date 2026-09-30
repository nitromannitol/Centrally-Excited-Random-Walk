import CERW.Support.Occupation.Cells
import CERW.Support.Occupation.CellSetVolume

/-!
# The integral of the cell local time

The cell local time is `ℓ_n(x)` on each occupied cell `C_x` and zero elsewhere. The cells have
volume one and the local times sum to `n`, so `∫ ℓ̃_n = n` over `D_n`, and over any measurable
set containing it. This is the identity `∫ ℓ̃_n = n` of the mass argument
(`eq:coarse-masserror`).
-/

namespace CERW.Support.Occupation

open MeasureTheory LatticeProb CERW

variable {d : ℕ}

/-- `∫_{D_n} ℓ̃_n = n`. -/
theorem setIntegral_cellLocalTime (X : ℕ → Site d) (n : ℕ) :
    ∫ v in cellSet X n, cellLocalTime X n v = n := by
  rw [cellSet]
  rw [integral_biUnion_finset (departureRange X n) (fun x _ => measurableSet_cell x)
    (fun x _ y _ hxy => cell_disjoint hxy)
    (fun x _ => (integrableOn_const (C := (localTime X n x : ℝ))
      (by rw [volume_cell]; norm_num)).congr_fun
        (fun v hv => (cellLocalTime_of_mem_cell X n hv).symm) (measurableSet_cell x))]
  trans ∑ x ∈ departureRange X n, (localTime X n x : ℝ)
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [setIntegral_congr_fun (measurableSet_cell x) (fun v hv => cellLocalTime_of_mem_cell X n hv),
      setIntegral_const]
    simp only [measureReal_def, volume_cell, ENNReal.toReal_one, one_smul]
  · rw [← Nat.cast_sum, sum_localTime_eq]

/-- `∫_S ℓ̃_n = n` for every measurable `S ⊇ D_n`. -/
theorem setIntegral_cellLocalTime_of_subset (X : ℕ → Site d) (n : ℕ)
    {S : Set (EuclideanSpace ℝ (Fin d))} (hS : MeasurableSet S) (hsub : cellSet X n ⊆ S) :
    ∫ v in S, cellLocalTime X n v = n := by
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hS hsub
    (fun v hv => cellLocalTime_eq_zero_of_not_mem X n hv.2)]
  exact setIntegral_cellLocalTime X n

end CERW.Support.Occupation
