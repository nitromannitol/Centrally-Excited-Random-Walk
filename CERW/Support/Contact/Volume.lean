import CERW.Model.Potential
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The volume of the range

`eq:volume` and the symmetric-difference estimate of `thm:fluctuations`, deterministically. If
`B(0, b) ⊆ D` with `|D \ B(0, b)| ≤ C₁ N^d Q` and `|b/N - a| ≤ C₁ Q`, then
`|(N⁻¹ D) Δ B(0, a)| + ||D|/N^d - ω_d a^d| ≤ C Q`. The rescaled set is `B(0, b/N)` together with a
set of volume `N^{-d} |D \ B(0, b)|`, and `|(b/N)^d - a^d| ≤ d max(b/N, a)^{d-1} |b/N - a|`.
-/

open scoped symmDiff Pointwise

namespace CERW.Support.Contact

open MeasureTheory CERW

variable {d : ℕ}

/-- The volume of a ball of nonnegative radius `r` in `ℝ^d` is `ω_d r^d`. -/
private lemma volume_ball_eq (hd : 1 ≤ d) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) =
      ENNReal.ofReal (unitBallVolume d * r ^ d) := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by
      rw [finrank_euclideanSpace_fin]; omega)
  have h1 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) =
      ENNReal.ofReal (unitBallVolume d) := by
    rw [unitBallVolume, ENNReal.ofReal_toReal]
    exact measure_ball_lt_top.ne
  rw [MeasureTheory.Measure.addHaar_ball (volume) (0 : EuclideanSpace ℝ (Fin d)) hr,
    finrank_euclideanSpace_fin, h1]
  rw [← ENNReal.ofReal_mul (pow_nonneg hr d)]
  congr 1
  ring

/-- For concentric balls of radii `s ≤ r`, the symmetric difference is the annulus, of volume
`ω_d (r^d - s^d)`. -/
private lemma volume_ball_symmDiff_of_le (hd : 1 ≤ d) {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s ∆
        Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) =
      ENNReal.ofReal (unitBallVolume d * (r ^ d - s ^ d)) := by
  have hr : 0 ≤ r := hs.trans hsr
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s ⊆
      Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r := Metric.ball_subset_ball hsr
  rw [symmDiff_of_le hsub]
  have hsmeas : MeasureTheory.NullMeasurableSet
      (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s) volume :=
    measurableSet_ball.nullMeasurableSet
  have hfin_s : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s) ≠ ⊤ :=
    measure_ball_lt_top.ne
  rw [MeasureTheory.measure_sdiff (μ := volume) hsub hsmeas hfin_s]
  rw [volume_ball_eq (r := r) hd hr, volume_ball_eq (r := s) hd hs]
  rw [← ENNReal.ofReal_sub _ (mul_nonneg (unitBallVolume_pos d).le (pow_nonneg hs d))]
  congr 1
  ring

/-- For two concentric balls, the symmetric difference has volume `ω_d |t^d - a^d|`. -/
private lemma volume_ball_symmDiff (hd : 1 ≤ d) {t a : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) t ∆
        Metric.ball (0 : EuclideanSpace ℝ (Fin d)) a) =
      ENNReal.ofReal (unitBallVolume d * |t ^ d - a ^ d|) := by
  rcases le_total t a with h | h
  · rw [volume_ball_symmDiff_of_le hd ht h]
    congr 1
    rw [abs_of_nonpos (sub_nonpos.mpr (pow_le_pow_left₀ ht h d))]
    ring
  · rw [symmDiff_comm, volume_ball_symmDiff_of_le hd ha h]
    congr 1
    rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ ha h d))]

/-- `|(N⁻¹ • D) Δ B(0, a)| + ||D|/N^d - ω_d a^d| ≤ C Q` under the inradius and excess-volume
bounds. -/
theorem exists_volume_symmDiff_add_le (hd : 1 ≤ d) {a C₁ : ℝ} (ha : 0 < a) (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Set (EuclideanSpace ℝ (Fin d))) (b N Q : ℝ), MeasurableSet D →
      volume D ≠ ⊤ → 0 ≤ b → 0 < N → 0 ≤ Q → Q ≤ 1 → Metric.ball 0 b ⊆ D →
      (volume (D \ Metric.ball 0 b)).toReal ≤ C₁ * N ^ d * Q → |b / N - a| ≤ C₁ * Q →
        volume ((N⁻¹ • D) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) a) +
            ENNReal.ofReal |(volume D).toReal / N ^ d - unitBallVolume d * a ^ d| ≤
          ENNReal.ofReal (C * Q) := by
  set K : ℝ := unitBallVolume d * (d : ℝ) * (a + C₁) ^ (d - 1) * C₁ + C₁ with hK
  set C : ℝ := 2 * K + 1 with hC
  have haC : 0 ≤ a + C₁ := by linarith
  have hK1nn : 0 ≤ unitBallVolume d * (d : ℝ) * (a + C₁) ^ (d - 1) * C₁ :=
    mul_nonneg (mul_nonneg (mul_nonneg (unitBallVolume_pos d).le (Nat.cast_nonneg d))
      (pow_nonneg haC _)) hC₁
  have hKnn : 0 ≤ K := by rw [hK]; exact add_nonneg hK1nn hC₁
  have hCpos : 0 < C := by rw [hC]; linarith
  refine ⟨C, hCpos, ?_⟩
  intro D b N Q hD hfin hb hN hQ0 hQ1 hball hexcess hdist
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hbt : 0 ≤ b / N := div_nonneg hb hN.le
  have hNpow_pos : 0 < N ^ d := pow_pos hN d
  have hNpow_nn : 0 ≤ N ^ d := hNpow_pos.le
  have hC1Q : 0 ≤ C₁ * Q := mul_nonneg hC₁ hQ0
  have hEmeas : MeasurableSet (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) :=
    hD.diff measurableSet_ball
  have hEfin : volume (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono Set.sdiff_subset)
  have hDunion : D = Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ∪
      (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) :=
    (Set.union_sdiff_cancel hball).symm
  have hvolD : volume D = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) +
      volume (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) := by
    conv_lhs => rw [hDunion]
    exact MeasureTheory.measure_union Set.disjoint_sdiff_right hEmeas
  have hvolball : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal =
      unitBallVolume d * b ^ d := by
    rw [volume_ball_eq (r := b) hd hb]
    exact ENNReal.toReal_ofReal (mul_nonneg hω.le (pow_nonneg hb d))
  have hDtoreal : (volume D).toReal =
      unitBallVolume d * b ^ d +
        (volume (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal := by
    rw [hvolD, ENNReal.toReal_add measure_ball_lt_top.ne hEfin, hvolball]
  have hmain : (volume D).toReal / N ^ d - unitBallVolume d * a ^ d =
      unitBallVolume d * ((b / N) ^ d - a ^ d) +
        (volume (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal / N ^ d := by
    rw [hDtoreal, add_div]
    have h1 : unitBallVolume d * b ^ d / N ^ d = unitBallVolume d * (b ^ d / N ^ d) := by ring
    rw [h1, (div_pow b N d).symm]
    ring
  have hK1bound : unitBallVolume d * |(b / N) ^ d - a ^ d| ≤
      unitBallVolume d * (d : ℝ) * (a + C₁) ^ (d - 1) * C₁ * Q := by
    have hba : b / N ≤ a + C₁ * Q := by
      have h1 := le_abs_self (b / N - a)
      linarith
    have hba1 : b / N ≤ a + C₁ := by
      have h2 : C₁ * Q ≤ C₁ := by
        calc C₁ * Q ≤ C₁ * 1 := mul_le_mul_of_nonneg_left hQ1 hC₁
          _ = C₁ := mul_one C₁
      linarith
    have hmaxnn : 0 ≤ max |b / N| |a| := le_trans (abs_nonneg _) (le_max_left _ _)
    have hmaxle : max |b / N| |a| ≤ a + C₁ := by
      rw [abs_of_nonneg hbt, abs_of_pos ha]
      exact max_le hba1 (by linarith)
    have hpowle : max |b / N| |a| ^ (d - 1) ≤ (a + C₁) ^ (d - 1) :=
      pow_le_pow_left₀ hmaxnn hmaxle (d - 1)
    have habs : |(b / N) ^ d - a ^ d| ≤
        C₁ * Q * (d : ℝ) * (a + C₁) ^ (d - 1) := by
      calc |(b / N) ^ d - a ^ d|
          ≤ |b / N - a| * (d : ℝ) * max |b / N| |a| ^ (d - 1) :=
            abs_pow_sub_pow_le (b / N) a d
        _ ≤ C₁ * Q * (d : ℝ) * (a + C₁) ^ (d - 1) := by
            gcongr
    calc unitBallVolume d * |(b / N) ^ d - a ^ d|
        ≤ unitBallVolume d * (C₁ * Q * (d : ℝ) * (a + C₁) ^ (d - 1)) :=
          mul_le_mul_of_nonneg_left habs hω.le
      _ = unitBallVolume d * (d : ℝ) * (a + C₁) ^ (d - 1) * C₁ * Q := by ring
  have hmbound : (volume (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal /
      N ^ d ≤ C₁ * Q := by
    rw [div_le_iff₀ hNpow_pos]
    rw [show C₁ * Q * N ^ d = C₁ * N ^ d * Q by ring]
    exact hexcess
  have hcombined : |(volume D).toReal / N ^ d - unitBallVolume d * a ^ d| ≤ K * Q := by
    calc |(volume D).toReal / N ^ d - unitBallVolume d * a ^ d|
        ≤ unitBallVolume d * |(b / N) ^ d - a ^ d| +
            (volume (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal / N ^ d := by
          rw [hmain]
          calc |unitBallVolume d * ((b / N) ^ d - a ^ d) +
                (volume (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal / N ^ d|
              ≤ |unitBallVolume d * ((b / N) ^ d - a ^ d)| +
                  |(volume (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal /
                    N ^ d| := abs_add_le _ _
            _ = unitBallVolume d * |(b / N) ^ d - a ^ d| +
                  (volume (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal /
                    N ^ d := by
                rw [abs_mul, abs_of_nonneg hω.le,
                  abs_of_nonneg (div_nonneg ENNReal.toReal_nonneg hNpow_nn)]
      _ ≤ unitBallVolume d * (d : ℝ) * (a + C₁) ^ (d - 1) * C₁ * Q + C₁ * Q :=
          add_le_add hK1bound hmbound
      _ = K * Q := by rw [hK]; ring
  have hB : ENNReal.ofReal |(volume D).toReal / N ^ d - unitBallVolume d * a ^ d| ≤
      ENNReal.ofReal (K * Q) := ENNReal.ofReal_le_ofReal hcombined
  have hsmulball : N⁻¹ • Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b =
      Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (b / N) := by
    rw [_root_.smul_ball (inv_ne_zero hN.ne') (0 : EuclideanSpace ℝ (Fin d)) b]
    simp only [smul_zero]
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hN.le)]
    congr 1
    rw [div_eq_inv_mul]
  have hsmul_eq : N⁻¹ • D = Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (b / N) ∪
      N⁻¹ • (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) := by
    calc N⁻¹ • D = N⁻¹ • (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ∪
          (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)) := by
          conv_lhs => rw [hDunion]
      _ = N⁻¹ • Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ∪
          N⁻¹ • (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) := by
          rw [Set.smul_set_union]
      _ = Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (b / N) ∪
          N⁻¹ • (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) := by rw [hsmulball]
  have hsub : (N⁻¹ • D) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) a ⊆
      (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (b / N) ∆
        Metric.ball (0 : EuclideanSpace ℝ (Fin d)) a) ∪
        N⁻¹ • (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) := by
    rw [hsmul_eq]
    intro x hx
    simp only [Set.mem_symmDiff, Set.mem_union] at hx ⊢
    tauto
  have hballsym : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (b / N) ∆
      Metric.ball (0 : EuclideanSpace ℝ (Fin d)) a) =
      ENNReal.ofReal (unitBallVolume d * |(b / N) ^ d - a ^ d|) :=
    volume_ball_symmDiff hd hbt ha.le
  have hscaledE : volume (N⁻¹ • (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)) ≤
      ENNReal.ofReal (C₁ * Q) := by
    rw [MeasureTheory.Measure.addHaar_smul (volume) (N⁻¹)
        (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b),
      finrank_euclideanSpace_fin,
      (ENNReal.ofReal_toReal hEfin).symm]
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hN.le) d)]
    have h1 : (N⁻¹) ^ d * (volume (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal =
        (volume (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal / N ^ d := by
      rw [inv_pow, div_eq_mul_inv]
      ring
    rw [h1]
    exact hmbound
  have hA : volume ((N⁻¹ • D) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) a) ≤
      ENNReal.ofReal (K * Q) := by
    calc volume ((N⁻¹ • D) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) a)
        ≤ volume ((Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (b / N) ∆
              Metric.ball (0 : EuclideanSpace ℝ (Fin d)) a) ∪
              N⁻¹ • (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)) := measure_mono hsub
      _ ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (b / N) ∆
              Metric.ball (0 : EuclideanSpace ℝ (Fin d)) a) +
            volume (N⁻¹ • (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)) :=
            measure_union_le _ _
      _ = ENNReal.ofReal (unitBallVolume d * |(b / N) ^ d - a ^ d|) +
            volume (N⁻¹ • (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)) := by
            rw [hballsym]
      _ ≤ ENNReal.ofReal (unitBallVolume d * |(b / N) ^ d - a ^ d|) +
            ENNReal.ofReal (C₁ * Q) := add_le_add le_rfl hscaledE
      _ = ENNReal.ofReal (unitBallVolume d * |(b / N) ^ d - a ^ d| + C₁ * Q) :=
          (ENNReal.ofReal_add (mul_nonneg hω.le (abs_nonneg _)) hC1Q).symm
      _ ≤ ENNReal.ofReal (unitBallVolume d * (d : ℝ) * (a + C₁) ^ (d - 1) * C₁ * Q +
            C₁ * Q) := ENNReal.ofReal_le_ofReal (add_le_add hK1bound le_rfl)
      _ = ENNReal.ofReal (K * Q) := by
          congr 1
          rw [hK]
          ring
  calc volume ((N⁻¹ • D) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) a) +
        ENNReal.ofReal |(volume D).toReal / N ^ d - unitBallVolume d * a ^ d|
      ≤ ENNReal.ofReal (K * Q) + ENNReal.ofReal (K * Q) := add_le_add hA hB
    _ = ENNReal.ofReal (K * Q + K * Q) :=
        (ENNReal.ofReal_add (mul_nonneg hKnn hQ0) (mul_nonneg hKnn hQ0)).symm
    _ = ENNReal.ofReal (2 * K * Q) := by congr 1; ring
    _ ≤ ENNReal.ofReal (C * Q) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hC]
        nlinarith [hQ0]

end CERW.Support.Contact
