module

public import CERW.Support.Outer.Radius.LatticeKernel

@[expose] public section

/-!
# Cell Weights

Integrating the radial weight over lattice cells gives comparable cell weights. Summing these cell
integrals transfers continuous potential bounds to the lattice.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- The radial weight `χ(s) = (1 + |s|)^{2-2d}`. -/
noncomputable def ev_chi (d : ℕ) (s : ℝ) : ℝ := (1 + |s|) ^ (2 - 2 * (d : ℝ))

/-- The radial weight is nonnegative. -/
lemma ev_chi_nonneg (s : ℝ) : 0 ≤ ev_chi d s :=
  Real.rpow_nonneg (by linarith [abs_nonneg s]) _

/-- The radial weight is measurable. -/
lemma ev_measurable_chi : Measurable (ev_chi d) := by
  unfold ev_chi
  fun_prop

/-- The weight of a norm is `(1 + ‖ζ‖)^{2-2d}`. -/
lemma ev_chi_norm (ζ : EuclideanSpace ℝ (Fin d)) :
    ev_chi d ‖ζ‖ = (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ)) := by
  rw [ev_chi, abs_norm]

/-- For `d ≥ 3` the radial weight is integrable on `ℝ^d`. -/
lemma ev_integrable_chi_norm (hd : 3 ≤ d) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => ev_chi d ‖ζ‖) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h := integrable_one_add_norm (E := EuclideanSpace ℝ (Fin d)) (μ := volume)
    (r := 2 * (d : ℝ) - 2) (by rw [finrank_euclideanSpace_fin]; linarith)
  refine h.congr (Filter.Eventually.of_forall fun ζ => ?_)
  show (1 + ‖ζ‖) ^ (-(2 * (d : ℝ) - 2)) = ev_chi d ‖ζ‖
  rw [ev_chi_norm, show -(2 * (d : ℝ) - 2) = 2 - 2 * (d : ℝ) by ring]

/-- The cell weight `a(y) = ∫_{C_y} χ(|y₀ - ζ|) dζ`. -/
noncomputable def ev_cellWeight (d : ℕ) (y₀ : EuclideanSpace ℝ (Fin d)) (y : Site d) :
    ℝ :=
  ∫ ζ in cell y, ev_chi d ‖y₀ - ζ‖

/-- Two-sided bounds for the integral over a unit cell of a function bounded on the cell. -/
lemma ev_setIntegral_cell_mem_Icc {G : EuclideanSpace ℝ (Fin d) → ℝ} (y : Site d)
    (hG : IntegrableOn G (cell y)) {lo hi : ℝ}
    (h : ∀ ζ ∈ cell y, lo ≤ G ζ ∧ G ζ ≤ hi) :
    lo ≤ ∫ ζ in cell y, G ζ ∧ ∫ ζ in cell y, G ζ ≤ hi := by
  have hvol : volume (cell y) ≠ ⊤ := by
    rw [CERW.Support.Occupation.volume_cell]
    exact ENNReal.one_ne_top
  have hmeas := CERW.Support.Occupation.measurableSet_cell (d := d) y
  have hreal : volume.real (cell y) = 1 := by
    rw [Measure.real, CERW.Support.Occupation.volume_cell]
    simp
  have hc : ∀ c : ℝ, IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) => c) (cell y) :=
    fun c => integrableOn_const hvol
  constructor
  · have := setIntegral_mono_on (hc lo) hG hmeas fun ζ hζ => (h ζ hζ).1
    rwa [setIntegral_const, hreal, one_smul] at this
  · have := setIntegral_mono_on hG (hc hi) hmeas fun ζ hζ => (h ζ hζ).2
    rwa [setIntegral_const, hreal, one_smul] at this

/-- For a point `ζ` of the cell of `y`, and a site `z` whose cell is near `y₀`, the distance
`|y₀ - ζ|` differs from `|z - y|` by at most `√d`. -/
lemma ev_abs_norm_sub_sub_euclidNorm_le {y₀ ζ : EuclideanSpace ℝ (Fin d)}
    {y z : Site d} (hζ : ζ ∈ cell y) (hz : ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2) :
    |‖y₀ - ζ‖ - euclidNorm (z - y)| ≤ Real.sqrt d := by
  have h1 := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hζ
  have hw : euclidNorm (z - y) = ‖toSpace z - toSpace y‖ := by
    rw [← norm_toSpace, CERW.Support.Occupation.toSpace_sub]
  set w : EuclideanSpace ℝ (Fin d) := toSpace z - toSpace y with hwdef
  set r : EuclideanSpace ℝ (Fin d) := (y₀ - toSpace z) + (toSpace y - ζ) with hr
  have hsplit : y₀ - ζ = w + r := by rw [hwdef, hr]; abel
  have hrn : ‖r‖ ≤ Real.sqrt d := by
    calc ‖r‖ ≤ ‖y₀ - toSpace z‖ + ‖toSpace y - ζ‖ := norm_add_le _ _
      _ ≤ Real.sqrt d / 2 + Real.sqrt d / 2 := by
          rw [norm_sub_rev y₀, norm_sub_rev (toSpace y)]
          exact add_le_add hz h1
      _ = Real.sqrt d := by ring
  have h3 := abs_norm_sub_norm_le (w + r) w
  rw [add_sub_cancel_left] at h3
  rw [hw, hsplit]
  exact h3.trans hrn

/-- The comparison of the cell weight with the lattice kernel, pointwise on the cell. -/
lemma ev_chi_cell_bounds (hd : 1 ≤ d) {y₀ ζ : EuclideanSpace ℝ (Fin d)} {y z : Site d}
    (hζ : ζ ∈ cell y) (hz : ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2) :
    ((1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))))⁻¹ * ev_kern d (z - y) ≤ ev_chi d ‖y₀ - ζ‖ ∧
      ev_chi d ‖y₀ - ζ‖ ≤ (1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - y) := by
  have hq : 2 - 2 * (d : ℝ) ≤ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have habs := ev_abs_norm_sub_sub_euclidNorm_le (y₀ := y₀) hζ hz
  have hr0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hs0 : 0 ≤ ‖y₀ - ζ‖ := norm_nonneg _
  have ht0 := LatticeProb.euclidNorm_nonneg (z - y)
  have hc : 0 < 1 + Real.sqrt d := by linarith
  have hcpos : 0 < (1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))) := Real.rpow_pos_of_pos hc _
  obtain ⟨habs1, habs2⟩ := abs_le.mp habs
  have hup := ev_rpow_le_mul_rpow_of_le hs0 ht0 hc hq
    (show 1 + euclidNorm (z - y) ≤ (1 + Real.sqrt d) * (1 + ‖y₀ - ζ‖) by
      linarith [mul_nonneg hr0 hs0])
  have hlow := ev_rpow_le_mul_rpow_of_le ht0 hs0 hc hq
    (show 1 + ‖y₀ - ζ‖ ≤ (1 + Real.sqrt d) * (1 + euclidNorm (z - y)) by
      linarith [mul_nonneg hr0 ht0])
  rw [ev_chi_norm]
  constructor
  · rw [inv_mul_le_iff₀ hcpos]
    exact hlow
  · exact hup

/-- Two-sided bounds for the cell weight by the lattice kernel. -/
lemma ev_cellWeight_bounds (hd : 3 ≤ d) {y₀ : EuclideanSpace ℝ (Fin d)} {z : Site d}
    (hz : ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2) (y : Site d) :
    ((1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))))⁻¹ * ev_kern d (z - y) ≤ ev_cellWeight d y₀ y ∧
      ev_cellWeight d y₀ y ≤ (1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - y) := by
  have hint : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => ev_chi d ‖y₀ - ζ‖) :=
    (ev_integrable_chi_norm hd).comp_sub_left y₀
  exact ev_setIntegral_cell_mem_Icc y hint.integrableOn fun ζ hζ =>
    ev_chi_cell_bounds (by omega) hζ hz

/-- Summing over the cells of a finite set of sites: if `Uf` varies by at most `M` across each
cell and is at least `-Cf` off the union of the cells, then the cell-weighted sum of the values
of `Uf` at the sites is at most the integral of `G Uf` plus `(M + Cf) ∫ G`. -/
lemma ev_sum_setIntegral_mul_le {G Uf : EuclideanSpace ℝ (Fin d) → ℝ}
    {S : Finset (Site d)} {M Cf : ℝ} (hG0 : ∀ ζ, 0 ≤ G ζ) (hG : Integrable G)
    (hGU : Integrable (fun ζ => G ζ * Uf ζ)) (hM : 0 ≤ M) (hCf : 0 ≤ Cf)
    (hmod : ∀ y ∈ S, ∀ ζ ∈ cell y, Uf (toSpace y) ≤ Uf ζ + M)
    (hfar : ∀ ζ ∉ ⋃ y ∈ S, cell y, -Cf ≤ Uf ζ) :
    ∑ y ∈ S, (∫ ζ in cell y, G ζ) * Uf (toSpace y) ≤
      (∫ ζ, G ζ * Uf ζ) + (M + Cf) * ∫ ζ, G ζ := by
  set F : EuclideanSpace ℝ (Fin d) → ℝ := fun ζ => G ζ * (Uf ζ + M + Cf) with hF
  have hFeq : F = fun ζ => G ζ * Uf ζ + (M + Cf) * G ζ := by
    funext ζ
    rw [hF]
    ring
  have hFint : Integrable F := by
    rw [hFeq]
    exact hGU.add (hG.const_mul _)
  have hVmeas : MeasurableSet (⋃ y ∈ S, cell y) :=
    Finset.measurableSet_biUnion S fun y _ => CERW.Support.Occupation.measurableSet_cell y
  have hterm : ∀ y ∈ S, (∫ ζ in cell y, G ζ) * Uf (toSpace y) ≤ ∫ ζ in cell y, F ζ := by
    intro y hy
    rw [← integral_mul_const]
    refine setIntegral_mono_on (hG.integrableOn.mul_const _) hFint.integrableOn
      (CERW.Support.Occupation.measurableSet_cell y) fun ζ hζ => ?_
    have h1 := mul_le_mul_of_nonneg_left (hmod y hy ζ hζ) (hG0 ζ)
    have h2 : G ζ * (Uf ζ + M) ≤ G ζ * (Uf ζ + M + Cf) :=
      mul_le_mul_of_nonneg_left (by linarith) (hG0 ζ)
    exact h1.trans h2
  have hsum : ∑ y ∈ S, ∫ ζ in cell y, F ζ = ∫ ζ in ⋃ y ∈ S, cell y, F ζ := by
    rw [integral_biUnion_finset S (fun y _ => CERW.Support.Occupation.measurableSet_cell y)
      (fun x _ y _ hxy => cell_disjoint hxy) (fun y _ => hFint.integrableOn)]
  have hcompl : 0 ≤ ∫ ζ in (⋃ y ∈ S, cell y)ᶜ, F ζ := by
    refine setIntegral_nonneg hVmeas.compl fun ζ hζ => ?_
    have := hfar ζ hζ
    exact mul_nonneg (hG0 ζ) (by linarith)
  have htot := integral_add_compl hVmeas hFint
  have hFval : ∫ ζ, F ζ = (∫ ζ, G ζ * Uf ζ) + (M + Cf) * ∫ ζ, G ζ := by
    rw [hFeq, integral_add hGU (hG.const_mul _), integral_const_mul]
  calc ∑ y ∈ S, (∫ ζ in cell y, G ζ) * Uf (toSpace y)
      ≤ ∑ y ∈ S, ∫ ζ in cell y, F ζ := Finset.sum_le_sum hterm
    _ = ∫ ζ in ⋃ y ∈ S, cell y, F ζ := hsum
    _ ≤ ∫ ζ, F ζ := by linarith
    _ = (∫ ζ, G ζ * Uf ζ) + (M + Cf) * ∫ ζ, G ζ := hFval

end CERW.Support.Outer.Radius
