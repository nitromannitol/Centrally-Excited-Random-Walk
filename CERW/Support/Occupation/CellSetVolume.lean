import CERW.Support.Occupation.CellVolume

/-!
# Volume of the cell set

The cell set `D_n` is a finite disjoint union of unit cells, so it is measurable and
`|D_n| = |A_n|`: the identity behind `∫ ℓ̃_n = n` and the mass argument of `prop:coarse`.
-/

namespace CERW.Support.Occupation

open MeasureTheory LatticeProb CERW

variable {d : ℕ}

/-- The cell set `D_n` is measurable. -/
theorem measurableSet_cellSet (X : ℕ → Site d) (n : ℕ) : MeasurableSet (cellSet X n) := by
  rw [cellSet]
  exact Finset.measurableSet_biUnion _ fun x _ => measurableSet_cell x

/-- The volume of `D_n` is the number of departed sites: `|D_n| = |A_n|`. -/
theorem volume_cellSet (X : ℕ → Site d) (n : ℕ) :
    volume (cellSet X n) = (departureRange X n).card := by
  rw [cellSet]
  rw [measure_biUnion_finset (fun x _ y _ hxy => cell_disjoint hxy)
        (fun x _ => measurableSet_cell x)]
  simp_rw [volume_cell]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

end CERW.Support.Occupation
