import CERW.Model.Space
import CERW.Model.Potential
import LatticeProb.Walk.Ball
import CERW.Generic.Kernel.RadialPacking
import CERW.Support.Occupation.CellWeight

/-!
# The lattice sum of `|x|` over a ball

Comparison with unit cells: `Σ_{|x| < r} |x| = (d ω_d/(d+1)) r^{d+1} + O(r^d)` and
`Σ_{|x| < r} |x|² = (d ω_d/(d+2)) r^{d+2} + O(r^{d+1})` for `r ≥ 1`, where `ω_d` is the volume
of the unit ball (`thm:sharp`, Step 1 of the proof of parts (i)–(ii);
`thm:moment-fluctuations`, Step 1).
-/

namespace CERW.Generic.Lattice

open LatticeProb MeasureTheory CERW CERW.Support.Occupation CERW.Generic.Kernel

variable {d : ℕ}

/-- The norm is integrable on a closed ball. -/
private lemma integrableOn_closedBall_norm (d : ℕ) (ρ : ℝ) :
    IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (Metric.closedBall 0 ρ) :=
  ContinuousOn.integrableOn_compact (ProperSpace.isCompact_closedBall 0 ρ)
    continuous_norm.continuousOn

/-- Every point of a cell is in the closed ball of radius `|x| + √d/2`. -/
private lemma cell_subset_closedBall {d : ℕ} (x : Site d) :
    cell x ⊆ Metric.closedBall 0 (euclidNorm x + Real.sqrt d / 2) := by
  intro v hv
  rw [mem_closedBall_zero_iff]
  calc ‖v‖ ≤ ‖toSpace x‖ + ‖v - toSpace x‖ := norm_le_norm_add_norm_sub' v (toSpace x)
    _ = euclidNorm x + ‖v - toSpace x‖ := by rw [norm_toSpace]
    _ ≤ euclidNorm x + Real.sqrt d / 2 := by
        gcongr
        exact norm_sub_toSpace_le_of_mem_cell hv

/-- The norm is integrable on a cell. -/
private lemma integrableOn_cell_norm {d : ℕ} (x : Site d) :
    IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (cell x) :=
  (integrableOn_closedBall_norm d (euclidNorm x + Real.sqrt d / 2)).mono_set
    (cell_subset_closedBall x)

/-- Comparing `euclidNorm x` with the integral of `‖v‖` over the cell of `x`. -/
private lemma abs_euclidNorm_sub_setIntegral_norm_le {d : ℕ} (x : Site d) :
    |euclidNorm x - ∫ v in cell x, ‖v‖| ≤ Real.sqrt d / 2 := by
  have hvol : volume (cell x) ≠ ⊤ := by rw [volume_cell]; exact ENNReal.one_ne_top
  have hint : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (cell x) :=
    integrableOn_cell_norm x
  have hupInt : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) =>
      euclidNorm x + Real.sqrt d / 2) (cell x) := integrableOn_const hvol
  have hloInt : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) =>
      euclidNorm x - Real.sqrt d / 2) (cell x) := integrableOn_const hvol
  have hupval : ∫ v in cell x, (euclidNorm x + Real.sqrt d / 2)
      = euclidNorm x + Real.sqrt d / 2 := by
    rw [setIntegral_const]
    simp only [measureReal_def, volume_cell, ENNReal.toReal_one, one_smul]
  have hloval : ∫ v in cell x, (euclidNorm x - Real.sqrt d / 2)
      = euclidNorm x - Real.sqrt d / 2 := by
    rw [setIntegral_const]
    simp only [measureReal_def, volume_cell, ENNReal.toReal_one, one_smul]
  have hbdd_hi : ∀ v : EuclideanSpace ℝ (Fin d), v ∈ cell x →
      ‖v‖ ≤ euclidNorm x + Real.sqrt d / 2 := by
    intro v hv
    calc ‖v‖ ≤ ‖toSpace x‖ + ‖v - toSpace x‖ :=
          norm_le_norm_add_norm_sub' v (toSpace x)
      _ = euclidNorm x + ‖v - toSpace x‖ := by rw [norm_toSpace]
      _ ≤ euclidNorm x + Real.sqrt d / 2 := by
          gcongr
          exact norm_sub_toSpace_le_of_mem_cell hv
  have hbdd_lo : ∀ v : EuclideanSpace ℝ (Fin d), v ∈ cell x →
      euclidNorm x - Real.sqrt d / 2 ≤ ‖v‖ := by
    intro v hv
    have h1 : ‖toSpace x‖ ≤ ‖v‖ + ‖toSpace x - v‖ :=
      norm_le_norm_add_norm_sub' (toSpace x) v
    rw [norm_toSpace] at h1
    have h2 : ‖toSpace x - v‖ = ‖v - toSpace x‖ := norm_sub_rev _ _
    rw [h2] at h1
    have h3 : ‖v - toSpace x‖ ≤ Real.sqrt d / 2 := norm_sub_toSpace_le_of_mem_cell hv
    linarith
  have hupper : ∫ v in cell x, ‖v‖ ≤ euclidNorm x + Real.sqrt d / 2 := by
    have h := setIntegral_mono_on hint hupInt (measurableSet_cell x) hbdd_hi
    exact h.trans (le_of_eq hupval)
  have hlower : euclidNorm x - Real.sqrt d / 2 ≤ ∫ v in cell x, ‖v‖ := by
    have h := setIntegral_mono_on hloInt hint (measurableSet_cell x) hbdd_lo
    exact (le_of_eq hloval.symm).trans h
  exact abs_le.mpr ⟨by linarith [hlower], by linarith [hupper]⟩

/-- The difference of the ball integrals of `‖v‖` between radii `r - c` and `r + c`. -/
private lemma ball_norm_sub_le {d : ℕ} (hd : 1 ≤ d) {r c : ℝ} (hc : 0 ≤ c) (hr : 1 ≤ r)
    (hcr : c ≤ r) {A B : ℝ}
    (hA : A = d * unitBallVolume d * (r + c) ^ (d + 1) / (d + 1))
    (hB : B = d * unitBallVolume d * (r - c) ^ (d + 1) / (d + 1)) :
    |A - B| ≤ d * unitBallVolume d * 2 * c * (1 + c) ^ d * r ^ d := by
  have hcoef_nn : 0 ≤ d * unitBallVolume d / (d + 1) := by
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg d) (unitBallVolume_pos d).le
    · positivity
  have hpow_le : (r - c) ^ (d + 1) ≤ (r + c) ^ (d + 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) (d + 1)
  have hexp_le : d * unitBallVolume d * (r - c) ^ (d + 1) / (d + 1)
      ≤ d * unitBallVolume d * (r + c) ^ (d + 1) / (d + 1) := by
    calc d * unitBallVolume d * (r - c) ^ (d + 1) / (d + 1)
        = d * unitBallVolume d / (d + 1) * (r - c) ^ (d + 1) := by ring
      _ ≤ d * unitBallVolume d / (d + 1) * (r + c) ^ (d + 1) :=
          mul_le_mul_of_nonneg_left hpow_le hcoef_nn
      _ = d * unitBallVolume d * (r + c) ^ (d + 1) / (d + 1) := by ring
  have hval : d * unitBallVolume d * (r + c) ^ (d + 1) / (d + 1)
      - d * unitBallVolume d * (r - c) ^ (d + 1) / (d + 1)
      ≤ d * unitBallVolume d * 2 * c * (1 + c) ^ d * r ^ d := by
    have hfac : d * unitBallVolume d * (r + c) ^ (d + 1) / (d + 1)
        - d * unitBallVolume d * (r - c) ^ (d + 1) / (d + 1)
        = d * unitBallVolume d / (d + 1)
            * ((r + c) ^ (d + 1) - (r - c) ^ (d + 1)) := by ring
    rw [hfac]
    have hpow : (r + c) ^ (d + 1) - (r - c) ^ (d + 1)
        ≤ 2 * c * ((d : ℝ) + 1) * (r + c) ^ d := by
      have h := abs_pow_sub_pow_le (r + c) (r - c) (d + 1)
      rw [Nat.add_sub_cancel] at h
      have hmax : max |r + c| |r - c| = r + c := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ r + c),
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ r - c)]
        exact max_eq_left (by linarith)
      rw [hmax] at h
      have hsub : |(r + c) - (r - c)| = 2 * c := by
        rw [show (r + c) - (r - c) = 2 * c by ring]
        exact abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * c)
      rw [hsub] at h
      push_cast at h
      rwa [abs_of_nonneg (sub_nonneg.mpr hpow_le)] at h
    have hrc_le : (r + c) ^ d ≤ (1 + c) ^ d * r ^ d := by
      have h1 : r + c ≤ (1 + c) * r := by
        have := mul_le_mul_of_nonneg_left hr hc
        linarith
      calc (r + c) ^ d ≤ ((1 + c) * r) ^ d := pow_le_pow_left₀ (by linarith) h1 d
        _ = (1 + c) ^ d * r ^ d := by rw [mul_pow]
    have hcoef2_nn : 0 ≤ d * unitBallVolume d * 2 * c :=
      mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (unitBallVolume_pos d).le)
        (by norm_num)) hc
    have hstep1 : d * unitBallVolume d / (d + 1)
        * ((r + c) ^ (d + 1) - (r - c) ^ (d + 1))
        ≤ d * unitBallVolume d / (d + 1)
            * (2 * c * ((d : ℝ) + 1) * (r + c) ^ d) :=
      mul_le_mul_of_nonneg_left hpow hcoef_nn
    have hstep2 : d * unitBallVolume d / (d + 1)
        * (2 * c * ((d : ℝ) + 1) * (r + c) ^ d)
        = d * unitBallVolume d * 2 * c * (r + c) ^ d := by
      have hd1ne : ((d : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    have hstep3 : d * unitBallVolume d * 2 * c * (r + c) ^ d
        ≤ d * unitBallVolume d * 2 * c * ((1 + c) ^ d * r ^ d) :=
      mul_le_mul_of_nonneg_left hrc_le hcoef2_nn
    calc d * unitBallVolume d / (d + 1)
            * ((r + c) ^ (d + 1) - (r - c) ^ (d + 1))
        ≤ d * unitBallVolume d / (d + 1)
            * (2 * c * ((d : ℝ) + 1) * (r + c) ^ d) := hstep1
      _ = d * unitBallVolume d * 2 * c * (r + c) ^ d := hstep2
      _ ≤ d * unitBallVolume d * 2 * c * ((1 + c) ^ d * r ^ d) := hstep3
      _ = d * unitBallVolume d * 2 * c * (1 + c) ^ d * r ^ d := by ring
  exact (abs_sub_le_iff.mpr
    ⟨by linarith [hA.le, hB.ge], by linarith [hB.le, hA.ge, hexp_le]⟩).trans hval

/-- `Σ_{x ∈ ℤ^d, |x| < r} |x| = (d ω_d/(d+1)) r^{d+1} + O(r^d)` for `r ≥ 1`. -/
theorem abs_sum_norm_sub_le {d : ℕ} (hd : 1 ≤ d) :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      |∑ x ∈ (ballFinset d r).filter (fun x => euclidNorm x < r), euclidNorm x
        - d * CERW.unitBallVolume d / (d + 1) * r ^ (d + 1)| ≤ C * r ^ d := by
  let c : ℝ := Real.sqrt d / 2
  have hc : c = Real.sqrt d / 2 := rfl
  have hcpos : 0 < c := by
    rw [hc]
    have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    exact div_pos (Real.sqrt_pos.mpr hdR) (by norm_num)
  let branchA : ℝ := d * unitBallVolume d * 2 * c * (1 + c) ^ d
  let branchB : ℝ := d * unitBallVolume d * (2 * c) ^ (d + 1) / (d + 1)
  let C : ℝ := branchA + branchB + (3 : ℝ) ^ d * c
  have hC : C = d * unitBallVolume d * 2 * c * (1 + c) ^ d
      + d * unitBallVolume d * (2 * c) ^ (d + 1) / (d + 1) + (3 : ℝ) ^ d * c := rfl
  refine ⟨C, ?_⟩
  intro r hr
  set A : Finset (Site d) := (ballFinset d r).filter (fun x => euclidNorm x < r) with hA
  set U : Set (EuclideanSpace ℝ (Fin d)) := ⋃ x ∈ A, cell x with hU
  have hA_norm : ∀ x ∈ A, euclidNorm x < r := by
    intro x hx
    rw [hA] at hx
    exact (Finset.mem_filter.mp hx).2
  have hUmeas : MeasurableSet U := by
    rw [hU]
    exact Finset.measurableSet_biUnion A (fun x _ => measurableSet_cell x)
  have hUsub : U ⊆ Metric.ball 0 (r + c) := by
    intro v hv
    rw [hU] at hv
    obtain ⟨x, hxA, hvx⟩ := Set.mem_iUnion₂.mp hv
    rw [mem_ball_zero_iff]
    calc ‖v‖ ≤ ‖toSpace x‖ + ‖v - toSpace x‖ :=
          norm_le_norm_add_norm_sub' v (toSpace x)
      _ = euclidNorm x + ‖v - toSpace x‖ := by rw [norm_toSpace]
      _ ≤ euclidNorm x + c := by
          rw [hc]
          gcongr
          exact norm_sub_toSpace_le_of_mem_cell hvx
      _ < r + c := by linarith [hA_norm x hxA]
  have hIntU : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) U := by
    refine Measure.integrableOn_of_bounded (M := r + c) ?_
      measurable_norm.aestronglyMeasurable ?_
    · exact ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hUsub)
    · filter_upwards [ae_restrict_mem hUmeas] with v hv
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v)]
      exact le_of_lt (mem_ball_zero_iff.mp (hUsub hv))
  have hUnion : ∫ v in U, ‖v‖ = ∑ x ∈ A, ∫ v in cell x, ‖v‖ := by
    rw [hU]
    exact integral_biUnion_finset A (fun x _ => measurableSet_cell x)
      (fun x _ y _ hxy => cell_disjoint hxy) (fun x _ => integrableOn_cell_norm x)
  have hstepA : |(∑ x ∈ A, euclidNorm x) - ∫ v in U, ‖v‖| ≤ (A.card : ℝ) * c := by
    rw [hUnion, ← Finset.sum_sub_distrib]
    calc |∑ x ∈ A, (euclidNorm x - ∫ v in cell x, ‖v‖)|
        ≤ ∑ x ∈ A, |euclidNorm x - ∫ v in cell x, ‖v‖| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ A, c :=
          Finset.sum_le_sum (fun x _ => by
            rw [hc]
            exact abs_euclidNorm_sub_setIntegral_norm_le x)
      _ = (A.card : ℝ) * c := by rw [Finset.sum_const, nsmul_eq_mul]
  have hAcard_le : (A.card : ℝ) ≤ (3 : ℝ) ^ d * r ^ d := by
    have h1 : A.card ≤ (ballFinset d r).card := by
      rw [hA]
      exact Finset.card_filter_le _ _
    have h2 : ((ballFinset d r).card : ℝ) ≤ (2 * r + 1) ^ d :=
      card_ballFinset_le d (by linarith)
    have h3 : (2 * r + 1) ≤ 3 * r := by linarith
    have h4 : (2 * r + 1) ^ d ≤ (3 * r) ^ d :=
      pow_le_pow_left₀ (by linarith : 0 ≤ 2 * r + 1) h3 d
    calc (A.card : ℝ) ≤ ((ballFinset d r).card : ℝ) := by exact_mod_cast h1
      _ ≤ (2 * r + 1) ^ d := h2
      _ ≤ (3 * r) ^ d := h4
      _ = (3 : ℝ) ^ d * r ^ d := by rw [mul_pow]
  have hcount : (A.card : ℝ) * c ≤ (3 : ℝ) ^ d * c * r ^ d :=
    (mul_le_mul_of_nonneg_right hAcard_le hcpos.le).trans_eq (by ring)
  have hbranchA_nn : 0 ≤ branchA := by
    rw [show branchA = d * unitBallVolume d * 2 * c * (1 + c) ^ d from rfl]
    have h1 : 0 ≤ d * unitBallVolume d * 2 * c :=
      mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (unitBallVolume_pos d).le)
        (by norm_num)) hcpos.le
    exact mul_nonneg h1 (pow_nonneg (by linarith) d)
  have hbranchB_nn : 0 ≤ branchB := by
    rw [show branchB = d * unitBallVolume d * (2 * c) ^ (d + 1) / (d + 1) from rfl]
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (unitBallVolume_pos d).le)
        (pow_nonneg (by linarith) (d + 1))
    · positivity
  set M : ℝ := ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖v‖ with hM
  have hMval : M = d * unitBallVolume d * r ^ (d + 1) / (d + 1) := by
    rw [hM]
    exact integral_ball_norm (d := d) (ρ := r) hd (by linarith)
  have hbound : |(∫ v in U, ‖v‖) - M| ≤ (branchA + branchB) * r ^ d := by
    rcases le_or_gt c r with hcr | hrc
    · have hlosub : Metric.ball 0 (r - c) ⊆ U := by
        intro v hv
        rw [hU]
        refine Set.mem_iUnion₂.mpr ⟨cellCenter v, ?_, mem_cell_cellCenter v⟩
        rw [hA, Finset.mem_filter]
        have hvlt : ‖v‖ < r - c := by
          have h := mem_ball_zero_iff.mp hv
          rwa [hc] at h
        have hxlt : euclidNorm (cellCenter v) < r := by
          have h1 : ‖toSpace (cellCenter v)‖ ≤ ‖v‖ + ‖toSpace (cellCenter v) - v‖ :=
            norm_le_norm_add_norm_sub' (toSpace (cellCenter v)) v
          rw [norm_toSpace] at h1
          have h2 : ‖toSpace (cellCenter v) - v‖ = ‖v - toSpace (cellCenter v)‖ :=
            norm_sub_rev _ _
          rw [h2] at h1
          have h3 : ‖v - toSpace (cellCenter v)‖ ≤ c := by
            rw [hc]
            exact norm_sub_toSpace_le_of_mem_cell (mem_cell_cellCenter v)
          linarith
        exact ⟨mem_ballFinset_iff.mpr hxlt.le, hxlt⟩
      have hInthi : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖)
          (Metric.ball 0 (r + c)) :=
        (integrableOn_closedBall_norm d (r + c)).mono_set Metric.ball_subset_closedBall
      have hIntlo : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖)
          (Metric.ball 0 (r - c)) :=
        (integrableOn_closedBall_norm d (r - c)).mono_set Metric.ball_subset_closedBall
      have hIntmid : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖)
          (Metric.ball 0 r) :=
        (integrableOn_closedBall_norm d r).mono_set Metric.ball_subset_closedBall
      have hTlo : ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r - c), ‖v‖
          ≤ ∫ v in U, ‖v‖ :=
        setIntegral_mono_set hIntU
          (Filter.Eventually.of_forall (fun v : EuclideanSpace ℝ (Fin d) => norm_nonneg v))
          (Filter.Eventually.of_forall hlosub)
      have hMlo : ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r - c), ‖v‖ ≤ M := by
        rw [hM]
        exact setIntegral_mono_set hIntmid
          (Filter.Eventually.of_forall (fun v : EuclideanSpace ℝ (Fin d) => norm_nonneg v))
          (Filter.Eventually.of_forall
            (fun v hv => Metric.ball_subset_ball (by linarith : r - c ≤ r) hv))
      have hThi : ∫ v in U, ‖v‖
          ≤ ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r + c), ‖v‖ :=
        setIntegral_mono_set hInthi
          (Filter.Eventually.of_forall (fun v : EuclideanSpace ℝ (Fin d) => norm_nonneg v))
          (Filter.Eventually.of_forall hUsub)
      have hMhi : M ≤ ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r + c), ‖v‖ := by
        rw [hM]
        exact setIntegral_mono_set hInthi
          (Filter.Eventually.of_forall (fun v : EuclideanSpace ℝ (Fin d) => norm_nonneg v))
          (Filter.Eventually.of_forall
            (fun v hv => Metric.ball_subset_ball (by linarith : r ≤ r + c) hv))
      have hboundA : |(∫ v in U, ‖v‖) - M| ≤ branchA * r ^ d := by
        rw [show branchA = d * unitBallVolume d * 2 * c * (1 + c) ^ d from rfl]
        have h3 : |(∫ v in U, ‖v‖) - M| ≤
            (∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r + c), ‖v‖)
              - (∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r - c), ‖v‖) :=
          abs_sub_le_iff.mpr ⟨sub_le_sub hThi hMlo, sub_le_sub hMhi hTlo⟩
        have hA' : ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r + c), ‖v‖
            = d * unitBallVolume d * (r + c) ^ (d + 1) / (d + 1) :=
          integral_ball_norm (d := d) (ρ := r + c) hd (by linarith)
        have hB' : ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r - c), ‖v‖
            = d * unitBallVolume d * (r - c) ^ (d + 1) / (d + 1) :=
          integral_ball_norm (d := d) (ρ := r - c) hd (by linarith)
        have h5 : (∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r + c), ‖v‖)
            - (∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r - c), ‖v‖)
            ≤ d * unitBallVolume d * 2 * c * (1 + c) ^ d * r ^ d :=
          (abs_le.mp (ball_norm_sub_le hd hcpos.le hr hcr hA' hB')).2
        exact h3.trans h5
      exact hboundA.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hbranchB_nn)
        (pow_nonneg (by linarith : 0 ≤ r) d))
    · have hInthi : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖)
          (Metric.ball 0 (r + c)) :=
        (integrableOn_closedBall_norm d (r + c)).mono_set Metric.ball_subset_closedBall
      have hThi : ∫ v in U, ‖v‖
          ≤ ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r + c), ‖v‖ :=
        setIntegral_mono_set hInthi
          (Filter.Eventually.of_forall (fun v : EuclideanSpace ℝ (Fin d) => norm_nonneg v))
          (Filter.Eventually.of_forall hUsub)
      have hMhi : M ≤ ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r + c), ‖v‖ := by
        rw [hM]
        exact setIntegral_mono_set hInthi
          (Filter.Eventually.of_forall (fun v : EuclideanSpace ℝ (Fin d) => norm_nonneg v))
          (Filter.Eventually.of_forall
            (fun v hv => Metric.ball_subset_ball (by linarith : r ≤ r + c) hv))
      have hTnonneg : 0 ≤ ∫ v in U, ‖v‖ :=
        setIntegral_nonneg hUmeas (fun v _ => norm_nonneg v)
      have hMnonneg : 0 ≤ M := by
        rw [hM]
        exact setIntegral_nonneg measurableSet_ball (fun v _ => norm_nonneg v)
      have hboundB : |(∫ v in U, ‖v‖) - M| ≤ branchB * r ^ d := by
        rw [show branchB = d * unitBallVolume d * (2 * c) ^ (d + 1) / (d + 1) from rfl]
        have h3 : |(∫ v in U, ‖v‖) - M|
            ≤ ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r + c), ‖v‖ := by
          have h1 : M - ∫ v in U, ‖v‖
              ≤ ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r + c), ‖v‖ := by
            simpa only [sub_zero] using sub_le_sub hMhi hTnonneg
          have h2 : (∫ v in U, ‖v‖) - M
              ≤ ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r + c), ‖v‖ := by
            simpa only [sub_zero] using sub_le_sub hThi hMnonneg
          exact abs_sub_le_iff.mpr ⟨h2, h1⟩
        have h4 : ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r + c), ‖v‖
            = d * unitBallVolume d * (r + c) ^ (d + 1) / (d + 1) :=
          integral_ball_norm (d := d) (ρ := r + c) hd (by linarith)
        have h3' : |(∫ v in U, ‖v‖) - M|
            ≤ d * unitBallVolume d * (r + c) ^ (d + 1) / (d + 1) :=
          h3.trans (le_of_eq h4)
        have hrp : r + c ≤ 2 * c := by linarith
        have hpow : (r + c) ^ (d + 1) ≤ (2 * c) ^ (d + 1) :=
          pow_le_pow_left₀ (by linarith : 0 ≤ r + c) hrp (d + 1)
        have hrpow : (1 : ℝ) ≤ r ^ d := one_le_pow₀ hr
        have hcoef : 0 ≤ d * unitBallVolume d / (d + 1) := by
          apply div_nonneg
          · exact mul_nonneg (Nat.cast_nonneg d) (unitBallVolume_pos d).le
          · positivity
        calc |(∫ v in U, ‖v‖) - M|
            ≤ d * unitBallVolume d * (r + c) ^ (d + 1) / (d + 1) := h3'
          _ = d * unitBallVolume d / (d + 1) * (r + c) ^ (d + 1) := by ring
          _ ≤ d * unitBallVolume d / (d + 1) * (2 * c) ^ (d + 1) := by gcongr
          _ ≤ d * unitBallVolume d / (d + 1) * (2 * c) ^ (d + 1) * r ^ d := by
              have hnn : 0 ≤ d * unitBallVolume d / (d + 1) * (2 * c) ^ (d + 1) :=
                mul_nonneg hcoef (pow_nonneg (by linarith) (d + 1))
              simpa using mul_le_mul_of_nonneg_left hrpow hnn
          _ = d * unitBallVolume d * (2 * c) ^ (d + 1) / (d + 1) * r ^ d := by ring
      exact hboundB.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hbranchA_nn)
        (pow_nonneg (by linarith : 0 ≤ r) d))
  have htri : |(∑ x ∈ A, euclidNorm x) - M|
      ≤ |(∑ x ∈ A, euclidNorm x) - ∫ v in U, ‖v‖| + |(∫ v in U, ‖v‖) - M| := by
    have h := abs_add_le ((∑ x ∈ A, euclidNorm x) - ∫ v in U, ‖v‖)
      ((∫ v in U, ‖v‖) - M)
    have heq : ((∑ x ∈ A, euclidNorm x) - ∫ v in U, ‖v‖) + ((∫ v in U, ‖v‖) - M)
        = (∑ x ∈ A, euclidNorm x) - M := by ring_nf
    rwa [heq] at h
  have hgoal : d * CERW.unitBallVolume d / (d + 1) * r ^ (d + 1) = M := by
    rw [hMval]
    ring
  rw [hgoal]
  calc |(∑ x ∈ A, euclidNorm x) - M|
      ≤ |(∑ x ∈ A, euclidNorm x) - ∫ v in U, ‖v‖| + |(∫ v in U, ‖v‖) - M| := htri
    _ ≤ (A.card : ℝ) * c + (branchA + branchB) * r ^ d := add_le_add hstepA hbound
    _ ≤ (3 : ℝ) ^ d * c * r ^ d + (branchA + branchB) * r ^ d :=
        add_le_add hcount le_rfl
    _ = ((3 : ℝ) ^ d * c + (branchA + branchB)) * r ^ d := by ring
    _ ≤ C * r ^ d := by
        rw [hC]
        exact le_of_eq (by ring)

end CERW.Generic.Lattice
