import CERW.Support.Geometry.TailBounds
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellSetVolume

/-!
# Counting shell sites by the tail

`eq:shell-count`: every departure cell `C_x` with `||x| - r| ≤ 3` lies in the shell
`r - b < |v| ≤ r + b` when `b > 3 + √d/2`. There `|v|^{1-d} ≥ (r + b)^{1-d}`, so the number of
such sites is at most `σ_d (r + b)^{d-1} [F(r - b) - F(r + b)]`, where `F` is the tail of the
cell set.
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

/-- A cell of a departure site in the shell `||x| - r| ≤ 3` lies in the annulus
`r - b < |v| ≤ r + b` inside the cell set, provided `b > 3 + √d/2`. -/
private theorem cell_subset_shell (X : ℕ → Site d) (n : ℕ) {r b : ℝ}
    (hb : 3 + Real.sqrt d / 2 < b) {x : Site d}
    (hx : x ∈ (departureRange X n).filter (fun x => |euclidNorm x - r| ≤ 3)) :
    cell x ⊆ cellSet X n ∩
      {v : EuclideanSpace ℝ (Fin d) | r - b < ‖v‖ ∧ ‖v‖ ≤ r + b} := by
  intro v hv
  refine ⟨Set.mem_iUnion₂.mpr ⟨x, (Finset.mem_filter.mp hx).1, hv⟩, ?_⟩
  have hx3 : |euclidNorm x - r| ≤ 3 := (Finset.mem_filter.mp hx).2
  have hdist : |‖v‖ - ‖toSpace x‖| ≤ Real.sqrt d / 2 :=
    (abs_norm_sub_norm_le v (toSpace x)).trans (norm_sub_toSpace_le_of_mem_cell hv)
  rw [norm_toSpace x] at hdist
  rw [abs_le] at hdist hx3
  constructor <;> linarith

/-- `eq:shell-count`: for `b > 3 + √d/2` and `r > b`, the departure sites `x` with
`||x| - r| ≤ 3` number at most `σ_d (r + b)^{d-1} [F(r - b) - F(r + b)]`. -/
theorem card_shell_le (hd : 1 ≤ d) (X : ℕ → Site d) (n : ℕ) {r b : ℝ}
    (hb : 3 + Real.sqrt d / 2 < b) (hrb : b < r) :
    (((departureRange X n).filter (fun x => |euclidNorm x - r| ≤ 3)).card : ℝ) ≤
      d * unitBallVolume d * (r + b) ^ ((d : ℝ) - 1) *
        (tail d (cellSet X n) (r - b) - tail d (cellSet X n) (r + b)) := by
  classical
  set S : Finset (Site d) :=
    (departureRange X n).filter (fun x => |euclidNorm x - r| ≤ 3) with hS
  set A : Set (EuclideanSpace ℝ (Fin d)) := ⋃ x ∈ S, cell x with hA
  set B : Set (EuclideanSpace ℝ (Fin d)) :=
    cellSet X n ∩ {v | r - b < ‖v‖ ∧ ‖v‖ ≤ r + b} with hB
  set f : EuclideanSpace ℝ (Fin d) → ℝ := fun v => ‖v‖ ^ (1 - (d : ℝ)) with hf
  set c : ℝ := (r + b) ^ (1 - (d : ℝ)) with hc
  have hb_pos : 0 < b := by linarith [Real.sqrt_nonneg d]
  have hrpb_pos : 0 < r + b := by linarith
  have hrb_pos : 0 < r - b := by linarith
  have hss' : r - b ≤ r + b := by linarith
  have hD : MeasurableSet (cellSet X n) := measurableSet_cellSet X n
  have hDb : Bornology.IsBounded (cellSet X n) :=
    (Metric.isBounded_ball (x := (0 : EuclideanSpace ℝ (Fin d)))
      (r := maxRadius X n + Real.sqrt d)).subset (cellSet_subset_ball hd X n)
  have hAB : A ⊆ B := by
    intro v hv
    rw [hA] at hv
    obtain ⟨x, hxS, hvx⟩ := Set.mem_iUnion₂.mp hv
    rw [hB]
    exact cell_subset_shell X n hb (by rwa [hS] at hxS) hvx
  have hBsub : B ⊆ cellSet X n ∩ {v | r - b < ‖v‖} := by
    intro v hv
    rw [hB] at hv
    exact ⟨hv.1, hv.2.1⟩
  have hIntB : IntegrableOn f B :=
    (CERW.Support.Geometry.integrableOn_tail hD hDb hrb_pos).mono_set hBsub
  have hIntAf : IntegrableOn f A := hIntB.mono_set hAB
  have hbound : ∀ v ∈ A, c ≤ f v := by
    intro v hv
    have hvB : v ∈ B := hAB hv
    rw [hB] at hvB
    have hvpos : 0 < ‖v‖ := lt_trans hrb_pos hvB.2.1
    have hvle : ‖v‖ ≤ r + b := hvB.2.2
    have hexp : 1 - (d : ℝ) ≤ 0 := by
      have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    have := Real.rpow_le_rpow_of_nonpos hvpos hvle hexp
    simpa only [hf, hc] using this
  have hAc_le : c * (S.card : ℝ) ≤ ∫ v in A, f v :=
    const_mul_card_le_integral_biUnion_cell S hIntAf (by simpa only [hA] using hbound)
  have hmonoAB : ∫ v in A, f v ≤ ∫ v in B, f v := by
    refine setIntegral_mono_set hIntB (Filter.Eventually.of_forall fun v => ?_) ?_
    · exact Real.rpow_nonneg (norm_nonneg v) _
    · exact Filter.Eventually.of_forall fun v hv => hAB hv
  have hcard_int : c * (S.card : ℝ) ≤ ∫ v in B, f v := le_trans hAc_le hmonoAB
  have hdω_ne : d * unitBallVolume d ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)))
      (ne_of_gt (unitBallVolume_pos d))
  have hInt_eq : ∫ v in B, f v = d * unitBallVolume d *
      (tail d (cellSet X n) (r - b) - tail d (cellSet X n) (r + b)) := by
    rw [hB, hf]
    rw [CERW.Support.Geometry.tail_sub_tail hD hDb hrb_pos hss']
    rw [← mul_assoc, mul_inv_cancel₀ hdω_ne, one_mul]
  have hcard_int' : c * (S.card : ℝ) ≤ d * unitBallVolume d *
      (tail d (cellSet X n) (r - b) - tail d (cellSet X n) (r + b)) := by
    rwa [hInt_eq] at hcard_int
  have hc_mul : (r + b) ^ ((d : ℝ) - 1) * c = 1 := by
    have h := Real.rpow_add hrpb_pos ((d : ℝ) - 1) (1 - (d : ℝ))
    rw [show ((d : ℝ) - 1) + (1 - (d : ℝ)) = 0 by ring, Real.rpow_zero] at h
    exact h.symm
  have hmul : (r + b) ^ ((d : ℝ) - 1) * (c * (S.card : ℝ)) ≤
      (r + b) ^ ((d : ℝ) - 1) * (d * unitBallVolume d *
        (tail d (cellSet X n) (r - b) - tail d (cellSet X n) (r + b))) :=
    mul_le_mul_of_nonneg_left hcard_int' (Real.rpow_nonneg hrpb_pos.le ((d : ℝ) - 1))
  have hleft : (r + b) ^ ((d : ℝ) - 1) * (c * (S.card : ℝ)) = (S.card : ℝ) := by
    rw [← mul_assoc, hc_mul, one_mul]
  have hright : (r + b) ^ ((d : ℝ) - 1) * (d * unitBallVolume d *
      (tail d (cellSet X n) (r - b) - tail d (cellSet X n) (r + b))) =
      d * unitBallVolume d * (r + b) ^ ((d : ℝ) - 1) *
        (tail d (cellSet X n) (r - b) - tail d (cellSet X n) (r + b)) := by
    ring
  have hfinal : (S.card : ℝ) ≤ d * unitBallVolume d * (r + b) ^ ((d : ℝ) - 1) *
      (tail d (cellSet X n) (r - b) - tail d (cellSet X n) (r + b)) := by
    calc (S.card : ℝ) = (r + b) ^ ((d : ℝ) - 1) * (c * (S.card : ℝ)) := hleft.symm
      _ ≤ (r + b) ^ ((d : ℝ) - 1) * (d * unitBallVolume d *
            (tail d (cellSet X n) (r - b) - tail d (cellSet X n) (r + b))) := hmul
      _ = d * unitBallVolume d * (r + b) ^ ((d : ℝ) - 1) *
            (tail d (cellSet X n) (r - b) - tail d (cellSet X n) (r + b)) := hright
  simpa only [hS] using hfinal

end CERW.Support.Coarse
