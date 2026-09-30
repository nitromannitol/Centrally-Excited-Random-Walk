import CERW.Support.Occupation.CellWeight
import CERW.Support.Occupation.CellSetVolume
import CERW.Support.Geometry.TailBasic

/-!
# The radial bracket in terms of the tail

The second inequality of `eq:radialbracket`:
`Σ_{x ∈ A_n, |x| > r - 2} ℓ_n(x) |x|^{2-2d} ≤ 2^{d-1} σ_d (r - 2)^{1-d} M_n F(r - b)` for
`b > 2 + √d/2` and `r - 2 ≥ √d`. Each local time is at most `M_n`, and
`|x|^{2-2d} ≤ (r - 2)^{1-d} |x|^{1-d}`.
The weighted integral of each departure cell is at least `2^{1-d}|x|^{1-d}`. These cells are
disjoint and lie in `D_n ∩ {|v| > r - b}`.
-/

namespace CERW.Support.Coarse

open MeasureTheory LatticeProb CERW CERW.Support.Occupation

variable {d : ℕ}

/-- `eq:radialbracket`, second inequality: for `b > 2 + √d/2`, `b < r` and `√d + 2 ≤ r`,
`Σ_{x ∈ A_n, |x| > r - 2} ℓ_n(x) |x|^{2-2d} ≤ 2^{d-1} σ_d (r - 2)^{1-d} M_n F(r - b)`. -/
theorem sum_localTime_rpow_le_tail (hd : 1 ≤ d) (X : ℕ → Site d) (n : ℕ) {r b : ℝ}
    (hb : 2 + Real.sqrt d / 2 < b) (hrb : b < r) (hr : Real.sqrt d + 2 ≤ r) :
    ∑ x ∈ (departureRange X n).filter (fun x => r - 2 < euclidNorm x),
        (localTime X n x : ℝ) * euclidNorm x ^ (2 - 2 * (d : ℝ)) ≤
      2 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) * (r - 2) ^ (1 - (d : ℝ)) *
        maxLocalTime X n * tail d (cellSet X n) (r - b) := by
  classical
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hc : 1 - (d : ℝ) ≤ 0 := by linarith
  have hr2 : 0 < r - 2 := by
    have hsp : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
    linarith
  have hrb_pos : 0 < r - b := by linarith
  have hw : 0 < (d : ℝ) * unitBallVolume d := mul_pos hdR (unitBallVolume_pos d)
  set S : Finset (Site d) :=
    (departureRange X n).filter (fun x => r - 2 < euclidNorm x) with hSdef
  have hSmem : ∀ x : Site d, x ∈ S ↔
      x ∈ departureRange X n ∧ r - 2 < euclidNorm x := by
    intro x
    rw [hSdef, Finset.mem_filter]
  have hC_nonneg : 0 ≤ (maxLocalTime X n : ℝ) * (r - 2) ^ (1 - (d : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (le_of_lt hr2) _)
  have hC_nonneg_full :
      0 ≤ (maxLocalTime X n : ℝ) * (r - 2) ^ (1 - (d : ℝ)) *
        (2 : ℝ) ^ ((d : ℝ) - 1) :=
    mul_nonneg hC_nonneg (Real.rpow_nonneg (by norm_num) _)
  -- Step 1: bound each local time by `M_n` and each `|x|`-power by `(r-2)`-power.
  have hstep1 : ∀ x ∈ S,
      (localTime X n x : ℝ) * euclidNorm x ^ (2 - 2 * (d : ℝ)) ≤
        (maxLocalTime X n : ℝ) * (r - 2) ^ (1 - (d : ℝ)) *
          euclidNorm x ^ (1 - (d : ℝ)) := by
    intro x hx
    rw [hSmem] at hx
    obtain ⟨_hxdep, hxgt⟩ := hx
    have hxpos : 0 < euclidNorm x := by linarith
    have hrpow : euclidNorm x ^ (2 - 2 * (d : ℝ)) =
        euclidNorm x ^ (1 - (d : ℝ)) * euclidNorm x ^ (1 - (d : ℝ)) := by
      rw [show (2 : ℝ) - 2 * (d : ℝ) = (1 - (d : ℝ)) + (1 - (d : ℝ)) by ring,
        Real.rpow_add hxpos]
    have hle_rpow : euclidNorm x ^ (1 - (d : ℝ)) ≤ (r - 2) ^ (1 - (d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hr2 (le_of_lt hxgt) hc
    have hM : (localTime X n x : ℝ) ≤ (maxLocalTime X n : ℝ) := by
      exact_mod_cast localTime_le_maxLocalTime X n x
    have h1d : 0 ≤ euclidNorm x ^ (1 - (d : ℝ)) :=
      Real.rpow_nonneg (euclidNorm_nonneg x) _
    calc (localTime X n x : ℝ) * euclidNorm x ^ (2 - 2 * (d : ℝ))
        = ((localTime X n x : ℝ) * euclidNorm x ^ (1 - (d : ℝ))) *
            euclidNorm x ^ (1 - (d : ℝ)) := by rw [hrpow]; ring
      _ ≤ ((maxLocalTime X n : ℝ) * euclidNorm x ^ (1 - (d : ℝ))) *
            euclidNorm x ^ (1 - (d : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM h1d) h1d
      _ = (maxLocalTime X n : ℝ) * (euclidNorm x ^ (1 - (d : ℝ)) *
            euclidNorm x ^ (1 - (d : ℝ))) := by ring
      _ ≤ (maxLocalTime X n : ℝ) * ((r - 2) ^ (1 - (d : ℝ)) *
            euclidNorm x ^ (1 - (d : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle_rpow h1d)
            (Nat.cast_nonneg _)
      _ = (maxLocalTime X n : ℝ) * (r - 2) ^ (1 - (d : ℝ)) *
            euclidNorm x ^ (1 - (d : ℝ)) := by ring
  -- Step 2: bound `|x|^{1-d}` by the cell integral using the cell-weight comparison.
  have hstep2 : ∀ x ∈ S,
      euclidNorm x ^ (1 - (d : ℝ)) ≤
        (2 : ℝ) ^ ((d : ℝ) - 1) * ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ)) := by
    intro x hx
    rw [hSmem] at hx
    obtain ⟨_hxdep, hxgt⟩ := hx
    have hxge : Real.sqrt d ≤ euclidNorm x := by linarith
    have h := (setIntegral_rpow_mem_Icc (d := d) hd hxge).1
    have hfac : (2 : ℝ) ^ ((d : ℝ) - 1) * (2 : ℝ) ^ (1 - (d : ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [show ((d : ℝ) - 1) + (1 - (d : ℝ)) = 0 by ring, Real.rpow_zero]
    calc euclidNorm x ^ (1 - (d : ℝ))
        = (2 : ℝ) ^ ((d : ℝ) - 1) *
            ((2 : ℝ) ^ (1 - (d : ℝ)) * euclidNorm x ^ (1 - (d : ℝ))) := by
          rw [← mul_assoc, hfac, one_mul]
      _ ≤ (2 : ℝ) ^ ((d : ℝ) - 1) * ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ)) :=
          mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  -- Combine the two termwise bounds.
  have hterm : ∀ x ∈ S,
      (localTime X n x : ℝ) * euclidNorm x ^ (2 - 2 * (d : ℝ)) ≤
        ((maxLocalTime X n : ℝ) * (r - 2) ^ (1 - (d : ℝ)) *
            (2 : ℝ) ^ ((d : ℝ) - 1)) *
          ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ)) := by
    intro x hx
    calc (localTime X n x : ℝ) * euclidNorm x ^ (2 - 2 * (d : ℝ))
        ≤ (maxLocalTime X n : ℝ) * (r - 2) ^ (1 - (d : ℝ)) *
            euclidNorm x ^ (1 - (d : ℝ)) := hstep1 x hx
      _ ≤ (maxLocalTime X n : ℝ) * (r - 2) ^ (1 - (d : ℝ)) *
            ((2 : ℝ) ^ ((d : ℝ) - 1) * ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ))) :=
          mul_le_mul_of_nonneg_left (hstep2 x hx) hC_nonneg
      _ = ((maxLocalTime X n : ℝ) * (r - 2) ^ (1 - (d : ℝ)) *
            (2 : ℝ) ^ ((d : ℝ) - 1)) *
          ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ)) := by ring
  have hDmeas : MeasurableSet (cellSet X n) := measurableSet_cellSet X n
  have hDbdd : Bornology.IsBounded (cellSet X n) :=
    Metric.isBounded_ball.subset (cellSet_subset_ball hd X n)
  have hintD : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (1 - (d : ℝ)))
      (cellSet X n ∩ {v | r - b < ‖v‖}) :=
    CERW.Support.Geometry.integrableOn_tail hDmeas hDbdd hrb_pos
  -- Each occupied cell lies in `D_n ∩ {|v| > r - b}`.
  have hcell_sub : ∀ x ∈ S, cell x ⊆ cellSet X n ∩ {v | r - b < ‖v‖} := by
    intro x hx v hv
    rw [hSmem] at hx
    obtain ⟨hxdep, hxgt⟩ := hx
    refine ⟨?_, ?_⟩
    · rw [cellSet]
      exact Set.mem_iUnion₂.mpr ⟨x, hxdep, hv⟩
    · have hdiff : |euclidNorm x - ‖v‖| ≤ Real.sqrt d / 2 := by
        calc |euclidNorm x - ‖v‖| = |‖toSpace x‖ - ‖v‖| := by rw [norm_toSpace]
          _ ≤ ‖toSpace x - v‖ := abs_norm_sub_norm_le (toSpace x) v
          _ = ‖v - toSpace x‖ := norm_sub_rev (toSpace x) v
          _ ≤ Real.sqrt d / 2 := norm_sub_toSpace_le_of_mem_cell hv
      have hlow : euclidNorm x - Real.sqrt d / 2 ≤ ‖v‖ := by
        have h' : euclidNorm x - ‖v‖ ≤ Real.sqrt d / 2 := (abs_le.mp hdiff).2
        linarith
      calc r - b < r - 2 - Real.sqrt d / 2 := by linarith
        _ < euclidNorm x - Real.sqrt d / 2 := by linarith
        _ ≤ ‖v‖ := hlow
  have hUnion_sub : (⋃ x ∈ S, cell x) ⊆ cellSet X n ∩ {v | r - b < ‖v‖} := by
    intro v hv
    rw [Set.mem_iUnion₂] at hv
    obtain ⟨x, hx, hvx⟩ := hv
    exact hcell_sub x hx hvx
  have hbiUnion : ∫ v in (⋃ x ∈ S, cell x), ‖v‖ ^ (1 - (d : ℝ)) =
      ∑ x ∈ S, ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ)) := by
    refine integral_biUnion_finset S (fun x _ => measurableSet_cell x) ?_ ?_
    · intro x _ y _ hxy
      exact cell_disjoint hxy
    · intro x hx
      exact hintD.mono_set (hcell_sub x hx)
  have hmono : ∫ v in (⋃ x ∈ S, cell x), ‖v‖ ^ (1 - (d : ℝ)) ≤
      ∫ v in cellSet X n ∩ {v | r - b < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ)) := by
    refine setIntegral_mono_set hintD (Filter.Eventually.of_forall fun v => ?_) ?_
    · exact Real.rpow_nonneg (norm_nonneg v) _
    · exact Filter.Eventually.of_forall fun v hv => hUnion_sub hv
  have htail : ∫ v in cellSet X n ∩ {v | r - b < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ)) =
      ((d : ℝ) * unitBallVolume d) * tail d (cellSet X n) (r - b) := by
    rw [tail]
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hw), one_mul]
  calc ∑ x ∈ S, (localTime X n x : ℝ) * euclidNorm x ^ (2 - 2 * (d : ℝ))
      ≤ ∑ x ∈ S, ((maxLocalTime X n : ℝ) * (r - 2) ^ (1 - (d : ℝ)) *
            (2 : ℝ) ^ ((d : ℝ) - 1)) *
            ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ)) := Finset.sum_le_sum hterm
    _ = ((maxLocalTime X n : ℝ) * (r - 2) ^ (1 - (d : ℝ)) *
            (2 : ℝ) ^ ((d : ℝ) - 1)) *
          ∑ x ∈ S, ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ)) :=
        (Finset.mul_sum S (fun x => ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ)))
          ((maxLocalTime X n : ℝ) * (r - 2) ^ (1 - (d : ℝ)) *
            (2 : ℝ) ^ ((d : ℝ) - 1))).symm
    _ = ((maxLocalTime X n : ℝ) * (r - 2) ^ (1 - (d : ℝ)) *
            (2 : ℝ) ^ ((d : ℝ) - 1)) *
          ∫ v in (⋃ x ∈ S, cell x), ‖v‖ ^ (1 - (d : ℝ)) := by rw [hbiUnion]
    _ ≤ ((maxLocalTime X n : ℝ) * (r - 2) ^ (1 - (d : ℝ)) *
            (2 : ℝ) ^ ((d : ℝ) - 1)) *
          ∫ v in cellSet X n ∩ {v | r - b < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hmono hC_nonneg_full
    _ = ((maxLocalTime X n : ℝ) * (r - 2) ^ (1 - (d : ℝ)) *
            (2 : ℝ) ^ ((d : ℝ) - 1)) *
          (((d : ℝ) * unitBallVolume d) * tail d (cellSet X n) (r - b)) := by rw [htail]
    _ = 2 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) * (r - 2) ^ (1 - (d : ℝ)) *
          maxLocalTime X n * tail d (cellSet X n) (r - b) := by ring

end CERW.Support.Coarse
