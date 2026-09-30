import CERW.Support.Geometry.TailBasic
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellVolume
import CERW.Support.Occupation.CellSetVolume

/-!
# Counting departure sites in an annulus by the tail

`eq:coarse-cellcount`, generalized: a set `S` of departure sites with `ρ < |x| < R'` has at most
`σ_d (R' + √d/2)^{d-1} F(ρ - √d/2)` elements. Its cells are disjoint unit cubes inside
`D_n ∩ {ρ - √d/2 < |v| < R' + √d/2}`, and there `|v|^{1-d} ≥ (R' + √d/2)^{1-d}`.
-/

namespace CERW.Support.Coarse

open MeasureTheory LatticeProb CERW CERW.Support.Occupation

open scoped ENNReal

variable {d : ℕ}

/-- A finite disjoint union of cells has volume equal to the number of its sites. -/
private theorem volume_biUnion_cell (S : Finset (Site d)) :
    volume (⋃ x ∈ S, cell x) = (S.card : ℝ≥0∞) := by
  rw [measure_biUnion_finset (fun x _ y _ hxy => cell_disjoint hxy)
        (fun x _ => measurableSet_cell x)]
  simp_rw [volume_cell]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- A constant `c` that is a pointwise lower bound on a finite disjoint union of unit cells
is at most the integral of the bounded function over that union. -/
private theorem const_mul_card_le_integral_biUnion_cell (S : Finset (Site d))
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {c : ℝ}
    (hfint : IntegrableOn f (⋃ x ∈ S, cell x))
    (hbound : ∀ v ∈ (⋃ x ∈ S, cell x), c ≤ f v) :
    c * (S.card : ℝ) ≤ ∫ v in (⋃ x ∈ S, cell x), f v := by
  have hAmeas : MeasurableSet (⋃ x ∈ S, cell x) :=
    Finset.measurableSet_biUnion S fun x _ => measurableSet_cell x
  have hvolA : (volume (⋃ x ∈ S, cell x)).toReal = (S.card : ℝ) := by
    rw [volume_biUnion_cell S, ENNReal.toReal_natCast]
  have hfine : volume (⋃ x ∈ S, cell x) ≠ ∞ := by
    rw [volume_biUnion_cell S]
    exact ENNReal.natCast_ne_top S.card
  have hIntAc : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) => c)
      (⋃ x ∈ S, cell x) := integrableOn_const hfine
  have hmono : ∫ v in (⋃ x ∈ S, cell x), c ≤ ∫ v in (⋃ x ∈ S, cell x), f v :=
    setIntegral_mono_on hIntAc hfint hAmeas hbound
  have hAc_eq : ∫ v in (⋃ x ∈ S, cell x), c = (S.card : ℝ) * c := by
    rw [setIntegral_const, smul_eq_mul, Measure.real_def, hvolA]
  calc c * (S.card : ℝ) = (S.card : ℝ) * c := by ring
    _ = ∫ v in (⋃ x ∈ S, cell x), c := hAc_eq.symm
    _ ≤ ∫ v in (⋃ x ∈ S, cell x), f v := hmono

/-- A cell of a departure site in the annulus `ρ < |x| < R'` lies in the annulus
`ρ - √d/2 < |v| < R' + √d/2` inside the cell set. -/
private theorem cell_subset_annulus (X : ℕ → Site d) (n : ℕ) {ρ_ R_ : ℝ}
    {S : Finset (Site d)} (hS : S ⊆ departureRange X n)
    (hSR : ∀ x ∈ S, ρ_ < euclidNorm x ∧ euclidNorm x < R_) {x : Site d} (hx : x ∈ S) :
    cell x ⊆ cellSet X n ∩
      {v : EuclideanSpace ℝ (Fin d) |
        ρ_ - Real.sqrt d / 2 < ‖v‖ ∧ ‖v‖ < R_ + Real.sqrt d / 2} := by
  intro v hv
  refine ⟨Set.mem_iUnion₂.mpr ⟨x, hS hx, hv⟩, ?_⟩
  have hx' := hSR x hx
  have hdist : |‖v‖ - ‖toSpace x‖| ≤ Real.sqrt d / 2 :=
    (abs_norm_sub_norm_le v (toSpace x)).trans (norm_sub_toSpace_le_of_mem_cell hv)
  rw [norm_toSpace x] at hdist
  rw [abs_le] at hdist
  constructor <;> linarith

/-- A set of departure sites in the annulus `ρ < |x| < R'` with `√d/2 < ρ ≤ R'` has at most
`σ_d (R' + √d/2)^{d-1} F(ρ - √d/2)` elements. -/
theorem card_le_tail (hd : 1 ≤ d) (X : ℕ → Site d) (n : ℕ) {S : Finset (Site d)}
    (hS : S ⊆ departureRange X n) {ρ R' : ℝ} (hρ : Real.sqrt d / 2 < ρ) (hρR : ρ ≤ R')
    (hSR : ∀ x ∈ S, ρ < euclidNorm x ∧ euclidNorm x < R') :
    (S.card : ℝ) ≤ d * unitBallVolume d * (R' + Real.sqrt d / 2) ^ ((d : ℝ) - 1) *
      tail d (cellSet X n) (ρ - Real.sqrt d / 2) := by
  classical
  set ρ' : ℝ := ρ - Real.sqrt d / 2 with hρ'
  set R'' : ℝ := R' + Real.sqrt d / 2 with hR''
  set U : Set (EuclideanSpace ℝ (Fin d)) := ⋃ x ∈ S, cell x with hU
  set B : Set (EuclideanSpace ℝ (Fin d)) := cellSet X n ∩ {v | ρ' < ‖v‖} with hB
  set f : EuclideanSpace ℝ (Fin d) → ℝ := fun v => ‖v‖ ^ (1 - (d : ℝ)) with hf
  set c : ℝ := R'' ^ (1 - (d : ℝ)) with hc
  have hρ'pos : 0 < ρ' := by
    rw [hρ']
    linarith
  have hR''pos : 0 < R'' := by
    rw [hR'']
    have hsqrt : 0 ≤ Real.sqrt d / 2 := by positivity
    linarith
  have hD : MeasurableSet (cellSet X n) := measurableSet_cellSet X n
  have hDb : Bornology.IsBounded (cellSet X n) :=
    (Metric.isBounded_ball (x := (0 : EuclideanSpace ℝ (Fin d)))
      (r := maxRadius X n + Real.sqrt d)).subset (cellSet_subset_ball hd X n)
  have hIntB : IntegrableOn f B := by
    rw [hB, hf]
    exact CERW.Support.Geometry.integrableOn_tail hD hDb hρ'pos
  have hUB : U ⊆ B := by
    intro v hv
    rw [hU] at hv
    obtain ⟨x, hxS, hvx⟩ := Set.mem_iUnion₂.mp hv
    rw [hB]
    have hsub := cell_subset_annulus X n hS hSR hxS hvx
    exact ⟨hsub.1, by rw [hρ']; exact hsub.2.1⟩
  have hIntU : IntegrableOn f U := hIntB.mono_set hUB
  have hbound : ∀ v ∈ U, c ≤ f v := by
    intro v hv
    rw [hU] at hv
    obtain ⟨x, hxS, hvx⟩ := Set.mem_iUnion₂.mp hv
    have hsub := cell_subset_annulus X n hS hSR hxS hvx
    have hvpos : 0 < ‖v‖ := lt_trans hρ'pos (by rw [hρ']; exact hsub.2.1)
    have hvle : ‖v‖ ≤ R'' := by
      rw [hR'']
      linarith [hsub.2.2]
    have hexp : 1 - (d : ℝ) ≤ 0 := by
      have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    have := Real.rpow_le_rpow_of_nonpos hvpos hvle hexp
    simpa only [hf, hc] using this
  have hAc_le : c * (S.card : ℝ) ≤ ∫ v in U, f v :=
    const_mul_card_le_integral_biUnion_cell S (by simpa only [hU] using hIntU)
      (by simpa only [hU] using hbound)
  have hmonoUB : ∫ v in U, f v ≤ ∫ v in B, f v := by
    refine setIntegral_mono_set hIntB (Filter.Eventually.of_forall fun v => ?_) ?_
    · exact Real.rpow_nonneg (norm_nonneg v) _
    · exact Filter.Eventually.of_forall fun v hv => hUB hv
  have hcard_int : c * (S.card : ℝ) ≤ ∫ v in B, f v := le_trans hAc_le hmonoUB
  have hdω_ne : d * unitBallVolume d ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)))
      (ne_of_gt (unitBallVolume_pos d))
  have hInt_eq : ∫ v in B, f v = d * unitBallVolume d * tail d (cellSet X n) ρ' := by
    rw [hB, hf, tail]
    rw [← mul_assoc, mul_inv_cancel₀ hdω_ne, one_mul]
  have hcard_int' : c * (S.card : ℝ) ≤ d * unitBallVolume d * tail d (cellSet X n) ρ' := by
    rwa [hInt_eq] at hcard_int
  have hc_mul : R'' ^ ((d : ℝ) - 1) * c = 1 := by
    have h := Real.rpow_add hR''pos ((d : ℝ) - 1) (1 - (d : ℝ))
    rw [show ((d : ℝ) - 1) + (1 - (d : ℝ)) = 0 by ring, Real.rpow_zero] at h
    exact h.symm
  have hmul : R'' ^ ((d : ℝ) - 1) * (c * (S.card : ℝ)) ≤
      R'' ^ ((d : ℝ) - 1) * (d * unitBallVolume d * tail d (cellSet X n) ρ') :=
    mul_le_mul_of_nonneg_left hcard_int' (Real.rpow_nonneg hR''pos.le ((d : ℝ) - 1))
  have hleft : R'' ^ ((d : ℝ) - 1) * (c * (S.card : ℝ)) = (S.card : ℝ) := by
    rw [← mul_assoc, hc_mul, one_mul]
  have hright : R'' ^ ((d : ℝ) - 1) * (d * unitBallVolume d * tail d (cellSet X n) ρ') =
      d * unitBallVolume d * R'' ^ ((d : ℝ) - 1) * tail d (cellSet X n) ρ' := by
    ring
  have hfinal : (S.card : ℝ) ≤ d * unitBallVolume d * R'' ^ ((d : ℝ) - 1) *
      tail d (cellSet X n) ρ' := by
    calc (S.card : ℝ) = R'' ^ ((d : ℝ) - 1) * (c * (S.card : ℝ)) := hleft.symm
      _ ≤ R'' ^ ((d : ℝ) - 1) * (d * unitBallVolume d * tail d (cellSet X n) ρ') := hmul
      _ = d * unitBallVolume d * R'' ^ ((d : ℝ) - 1) * tail d (cellSet X n) ρ' := hright
  simpa only [hρ', hR''] using hfinal

end CERW.Support.Coarse
