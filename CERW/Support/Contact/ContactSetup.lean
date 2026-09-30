import CERW.Support.Contact.ContactCell
import CERW.Support.Geometry.CellModulus
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellSetVolume

/-!
# The contact setup

For a path from the origin with `n ≥ 1` and `D_n ⊆ B(0, R)`, `R ≥ 1`, let
`b = inf {|y| : y ∉ D_n}`. The origin is a departure site, so `B(0, 1/2) ⊆ D_n` and `b > 0`.
`exists_contact_cell` gives `B(0, b) ⊆ D_n`, a point `y₀` with `|y₀| = b`, and an unvisited site
`z` with `|z - y₀| ≤ √d/2` and `|z| ≥ b`. Since `|y₀| ≤ R` and `|y₀ - z| ≤ √d`, the cell modulus
`exists_potential_cell_modulus` gives `|U(y₀) - U(z)| ≤ C ε log(R + 2)`.
-/

namespace CERW.Support.Contact

open MeasureTheory LatticeProb CERW

variable {d : ℕ}

/-- If the origin is a departure site, every point outside `D_n` lies at distance at least
`1/2` from the origin. -/
private theorem half_le_norm_of_not_mem_cellSet {X : ℕ → Site d} {n : ℕ} (hn : 1 ≤ n)
    (hX0 : X 0 = 0) {y : EuclideanSpace ℝ (Fin d)} (hy : y ∉ cellSet X n) :
    (1 / 2 : ℝ) ≤ ‖y‖ := by
  by_contra h
  rw [not_le] at h
  have h0 : (0 : Site d) ∈ departureRange X n := by
    rw [mem_departureRange_iff, localTime, Finset.card_pos]
    exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hX0⟩⟩
  have hy_cell : y ∈ cell (0 : Site d) := by
    intro i
    have hi : |y i| < 1 / 2 := by
      have hle : ‖y i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
      rw [Real.norm_eq_abs] at hle
      linarith
    constructor <;> simp only [Pi.zero_apply, Int.cast_zero] <;>
      linarith [(abs_lt.mp hi).1, (abs_lt.mp hi).2]
  exact hy (by rw [cellSet]; exact Set.mem_iUnion₂.mpr ⟨0, h0, hy_cell⟩)

/-- Inradius and contact cell of `D_n` for a path with `X 0 = 0` and `n ≥ 1`: the inradius is
positive and at most `R`, `B(0, b) ⊆ D_n`, and there are a contact point `y₀` and an unvisited
site `z` with `b ≤ |z| ≤ b + √d/2` and `|z - y₀| ≤ √d/2`. -/
private theorem exists_contact_setup_core (hd : 2 ≤ d) (X : ℕ → Site d) (n : ℕ) (R : ℝ)
    (hn : 1 ≤ n) (hX0 : X 0 = 0) (hR : 1 ≤ R)
    (hDsub : cellSet X n ⊆ Metric.ball 0 R) :
    let b : ℝ := sInf ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) '' (cellSet X n)ᶜ)
    0 < b ∧ b ≤ R ∧ Metric.ball 0 b ⊆ cellSet X n ∧
      ∃ y₀ : EuclideanSpace ℝ (Fin d), ‖y₀‖ = b ∧
        ∃ z : Site d, localTime X n z = 0 ∧ b ≤ euclidNorm z ∧
          euclidNorm z ≤ b + Real.sqrt d / 2 ∧ ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2 := by
  dsimp only
  set b : ℝ := sInf ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) '' (cellSet X n)ᶜ)
    with hbdef
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  obtain ⟨y₁, hy₁⟩ :=
    (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin d))) (r := R)).mpr hRpos.le
  have hy₁norm : ‖y₁‖ = R := by
    simpa using (mem_sphere_iff_norm.mp hy₁)
  have hy₁c : y₁ ∉ cellSet X n := by
    intro hyD
    have hmem := hDsub hyD
    rw [Metric.mem_ball, dist_zero_right] at hmem
    linarith
  have hne : ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) '' (cellSet X n)ᶜ).Nonempty :=
    ⟨‖y₁‖, ⟨y₁, hy₁c, rfl⟩⟩
  have hbdd : BddBelow ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) '' (cellSet X n)ᶜ) :=
    ⟨0, by rintro r ⟨y, -, rfl⟩; exact norm_nonneg y⟩
  have hb_ge : (1 / 2 : ℝ) ≤ b := by
    rw [hbdef]
    exact le_csInf hne fun r ⟨y, hyc, hyr⟩ => hyr ▸ half_le_norm_of_not_mem_cellSet hn hX0 hyc
  have hb_le_R : b ≤ R := by
    rw [hbdef]
    exact (csInf_le hbdd ⟨y₁, hy₁c, rfl⟩).trans_eq hy₁norm
  obtain ⟨hball, y₀, hy₀norm, z, hz0, hzy, hbz⟩ :=
    exists_contact_cell (by omega : 1 ≤ d) X n
  have hupper : euclidNorm z ≤ b + Real.sqrt d / 2 := by
    calc euclidNorm z = ‖toSpace z‖ := (norm_toSpace z).symm
      _ ≤ ‖y₀‖ + ‖toSpace z - y₀‖ := norm_le_norm_add_norm_sub' (toSpace z) y₀
      _ ≤ b + Real.sqrt d / 2 := by linarith [hy₀norm, hzy]
  exact ⟨lt_of_lt_of_le (by norm_num) hb_ge, hb_le_R, hball, y₀, hy₀norm, z, hz0, hbz, hupper,
    hzy⟩

/-- The contact setup: the inradius `b` is positive, `B(0, b) ⊆ D_n`, and there are a contact
point `y₀` and an unvisited site `z` with `b ≤ |z| ≤ b + √d/2` and
`|U(y₀) - U(z)| ≤ C ε log(R + 2)`. -/
theorem exists_contact_setup (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 ≤ ε → ∀ (X : ℕ → Site d) (n : ℕ) (R : ℝ), 1 ≤ n → X 0 = 0 →
      1 ≤ R → cellSet X n ⊆ Metric.ball 0 R →
      let b : ℝ := sInf ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) '' (cellSet X n)ᶜ)
      0 < b ∧ Metric.ball 0 b ⊆ cellSet X n ∧ ∃ y₀ : EuclideanSpace ℝ (Fin d), ‖y₀‖ = b ∧
        ∃ z : Site d, localTime X n z = 0 ∧ b ≤ euclidNorm z ∧
          euclidNorm z ≤ b + Real.sqrt d / 2 ∧
          |potential d ε (cellSet X n) y₀ - potential d ε (cellSet X n) (toSpace z)|
            ≤ C * ε * Real.log (R + 2) := by
  obtain ⟨C, hC, hmod⟩ := CERW.Support.Geometry.exists_potential_cell_modulus hd
  refine ⟨C, hC, ?_⟩
  intro ε hε X n R hn hX0 hR hDsub
  dsimp only
  set b : ℝ := sInf ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) '' (cellSet X n)ᶜ)
    with hbdef
  obtain ⟨hbpos, hbleR, hball, y₀, hy₀norm, z, hz0, hbz, hupper, hzydist⟩ :=
    exists_contact_setup_core hd X n R hn hX0 hR hDsub
  refine ⟨hbpos, hball, y₀, hy₀norm, z, hz0, hbz, hupper, ?_⟩
  have hy₀_le : ‖y₀‖ ≤ 2 * R := by
    rw [hy₀norm]
    linarith
  have hyz : ‖y₀ - toSpace z‖ ≤ Real.sqrt d := by
    rw [norm_sub_rev]
    linarith [hzydist, Real.sqrt_nonneg d]
  exact hmod ε hε R hR (cellSet X n) (CERW.Support.Occupation.measurableSet_cellSet X n)
    hDsub y₀ (toSpace z) hy₀_le hyz

end CERW.Support.Contact
