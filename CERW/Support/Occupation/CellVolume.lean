import CERW.Model.Occupation
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Volume of cells

Each half-open unit cell `C_x = x + [-1/2, 1/2)^d` is measurable with volume one: it is the
preimage of a product of unit intervals under the measure-preserving identification of
`EuclideanSpace ℝ (Fin d)` with `Fin d → ℝ`.
-/

namespace CERW.Support.Occupation

open MeasureTheory LatticeProb CERW

variable {d : ℕ}

/-- A cell is the preimage of a product of half-open unit intervals under the coordinate
identification `WithLp.ofLp`. -/
theorem cell_eq_preimage (x : Site d) :
    cell x = WithLp.ofLp ⁻¹' (Set.univ.pi fun i =>
      Set.Ico (((x i : ℤ) : ℝ) - 1 / 2) (((x i : ℤ) : ℝ) + 1 / 2)) := by
  ext v
  simp only [cell, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
    Set.mem_Ico, true_implies]

/-- A cell is measurable. -/
theorem measurableSet_cell (x : Site d) : MeasurableSet (cell x) := by
  have hbox : MeasurableSet (Set.univ.pi fun i =>
      Set.Ico (((x i : ℤ) : ℝ) - 1 / 2) (((x i : ℤ) : ℝ) + 1 / 2)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ico
  rw [cell_eq_preimage]
  exact (PiLp.volume_preserving_ofLp (Fin d)).measurable hbox

/-- A cell has volume one. -/
theorem volume_cell (x : Site d) : volume (cell x) = 1 := by
  have hbox : MeasurableSet (Set.univ.pi fun i =>
      Set.Ico (((x i : ℤ) : ℝ) - 1 / 2) (((x i : ℤ) : ℝ) + 1 / 2)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ico
  rw [cell_eq_preimage]
  rw [(PiLp.volume_preserving_ofLp (Fin d)).measure_preimage hbox.nullMeasurableSet]
  rw [Real.volume_pi_Ico]
  have hsub : ∀ i, ENNReal.ofReal ((((x i : ℤ) : ℝ) + 1 / 2)
      - (((x i : ℤ) : ℝ) - 1 / 2)) = 1 := by
    intro i
    have h : (((x i : ℤ) : ℝ) + 1 / 2) - (((x i : ℤ) : ℝ) - 1 / 2) = 1 := by
      ring
    rw [h, ENNReal.ofReal_one]
  simp only [hsub, Finset.prod_const_one]

end CERW.Support.Occupation
