import Mathlib.Analysis.InnerProductSpace.PiL2
import LatticeProb.Walk.Ball

/-!
# The lattice inside Euclidean space

A site of `ℤ^d` is embedded in `ℝ^d = EuclideanSpace ℝ (Fin d)` by `toSpace`, and its
Euclidean norm `|x|` is the library's `euclidNorm`. The half-open unit cell
`C_x = x + [-1/2, 1/2)^d` is `cell x`; every point of `ℝ^d` lies in exactly one cell, the
cell of `cellCenter v`. The direction `u_v = v/|v|`, with the paper's convention `u_0 = 0`,
is `unitDir`.
-/

namespace CERW

open LatticeProb

variable {d : ℕ}

/-- The embedding of a lattice site into `ℝ^d`. -/
noncomputable def toSpace (x : Site d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => ((x i : ℤ) : ℝ))

/-- The coordinates of an embedded site are its integer coordinates. -/
@[simp]
theorem toSpace_apply (x : Site d) (i : Fin d) : toSpace x i = ((x i : ℤ) : ℝ) :=
  rfl

/-- The Euclidean norm of an embedded site is the library's `euclidNorm`. -/
theorem norm_toSpace (x : Site d) : ‖toSpace x‖ = euclidNorm x := by
  rw [EuclideanSpace.norm_eq, euclidNorm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs]
  rfl

/-- The direction `u_v = v/|v|`, which is `0` at `v = 0` as the paper stipulates. -/
noncomputable def unitDir (v : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ‖v‖⁻¹ • v

/-- The direction of the origin is zero. -/
@[simp]
theorem unitDir_zero : unitDir (0 : EuclideanSpace ℝ (Fin d)) = 0 := by
  simp [unitDir]

/-- A direction has norm at most one. -/
theorem norm_unitDir_le (v : EuclideanSpace ℝ (Fin d)) : ‖unitDir v‖ ≤ 1 := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · rw [unitDir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

/-- The half-open unit cell `C_x = x + [-1/2, 1/2)^d` of a lattice site. -/
def cell (x : Site d) : Set (EuclideanSpace ℝ (Fin d)) :=
  {v | ∀ i, ((x i : ℤ) : ℝ) - 1 / 2 ≤ v i ∧ v i < ((x i : ℤ) : ℝ) + 1 / 2}

/-- The lattice site whose cell contains `v`: coordinatewise, `⌊v_i + 1/2⌋`. -/
noncomputable def cellCenter (v : EuclideanSpace ℝ (Fin d)) : Site d :=
  fun i => ⌊v i + 1 / 2⌋

/-- Every point lies in the cell of its `cellCenter`. -/
theorem mem_cell_cellCenter (v : EuclideanSpace ℝ (Fin d)) : v ∈ cell (cellCenter v) := by
  intro i
  have h₁ := Int.floor_le (v i + 1 / 2)
  have h₂ := Int.lt_floor_add_one (v i + 1 / 2)
  simp only [cellCenter]
  constructor <;> linarith

/-- A point lies in the cell of a site only if that site is its `cellCenter`: the cells are
disjoint. -/
theorem eq_cellCenter_of_mem_cell {x : Site d} {v : EuclideanSpace ℝ (Fin d)}
    (h : v ∈ cell x) : x = cellCenter v := by
  funext i
  obtain ⟨h₁, h₂⟩ := h i
  simp only [cellCenter]
  symm
  rw [Int.floor_eq_iff]
  constructor <;> linarith

/-- Membership in a cell is equality of the cell's site with the `cellCenter`. -/
theorem mem_cell_iff {x : Site d} {v : EuclideanSpace ℝ (Fin d)} :
    v ∈ cell x ↔ cellCenter v = x :=
  ⟨fun h => (eq_cellCenter_of_mem_cell h).symm, fun h => h ▸ mem_cell_cellCenter v⟩

/-- Cells of distinct sites are disjoint. -/
theorem cell_disjoint {x y : Site d} (h : x ≠ y) : Disjoint (cell x) (cell y) :=
  Set.disjoint_left.mpr fun _ hx hy =>
    h ((eq_cellCenter_of_mem_cell hx).trans (eq_cellCenter_of_mem_cell hy).symm)

/-- An embedded site lies in its own cell. -/
theorem toSpace_mem_cell (x : Site d) : toSpace x ∈ cell x := by
  intro i
  simp only [toSpace_apply]
  constructor <;> linarith

end CERW
