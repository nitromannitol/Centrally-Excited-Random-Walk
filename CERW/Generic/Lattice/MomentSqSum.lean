import CERW.Model.Space
import CERW.Model.Potential
import LatticeProb.Walk.Ball
import CERW.Generic.Kernel.RadialPower
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellVolume

/-!
# The lattice sum of `|x|²` over a ball

Comparison with unit cells: `Σ_{|x| < r} |x| = (d ω_d/(d+1)) r^{d+1} + O(r^d)` and
`Σ_{|x| < r} |x|² = (d ω_d/(d+2)) r^{d+2} + O(r^{d+1})` for `r ≥ 1`, where `ω_d` is the
volume of the unit ball (`thm:sharp`, Step 1 of the proof of parts (i)–(ii);
`thm:moment-fluctuations`, Step 1).
-/

namespace CERW.Generic.Lattice

open MeasureTheory Filter LatticeProb CERW

variable {d : ℕ}

/-- The integral of `|v|²` over the ball of radius `ρ > 0` is `d ω_d ρ^{d+2}/(d+2)`. -/
private lemma setIntegral_norm_sq_ball (hd : 1 ≤ d) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ, ‖v‖ ^ 2
      = d * CERW.unitBallVolume d / (d + 2) * ρ ^ (d + 2) := by
  obtain ⟨_, h⟩ := CERW.Generic.Kernel.integrableOn_ball_rpow_neg_and_integral_eq
    (d := d) hd (s := -2) (by have : (0:ℝ) ≤ d := Nat.cast_nonneg d; linarith) hρ
  simp only [neg_neg, Real.rpow_ofNat] at h
  rw [h, ← Real.rpow_natCast]
  have hexp : (d : ℝ) - -2 = (d : ℝ) + 2 := by ring
  rw [hexp]
  push_cast
  ring

/-- `|v|²` is integrable on the ball `B(0,ρ)` for `ρ > 0`. -/
private lemma integrableOn_norm_sq_ball (hd : 1 ≤ d) {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ 2) (Metric.ball 0 ρ) := by
  have h := (CERW.Generic.Kernel.integrableOn_ball_rpow_neg_and_integral_eq
    (d := d) hd (s := -2) (by have : (0:ℝ) ≤ d := Nat.cast_nonneg d; linarith) hρ).1
  simpa only [neg_neg, Real.rpow_ofNat] using h

/-- `|v|²` is integrable on every unit cell. -/
private lemma integrableOn_norm_sq_cell (hd : 1 ≤ d) (x : Site d) :
    IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ 2) (cell x) := by
  have hρ : 0 < euclidNorm x + Real.sqrt d / 2 + 1 := by
    have := euclidNorm_nonneg x; have := Real.sqrt_nonneg d; linarith
  refine (integrableOn_norm_sq_ball hd hρ).mono_set ?_
  intro v hv
  rw [Metric.mem_ball, dist_zero_right]
  have hvx := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hv
  calc ‖v‖ ≤ ‖toSpace x‖ + ‖v - toSpace x‖ := norm_le_norm_add_norm_sub' v (toSpace x)
    _ = euclidNorm x + ‖v - toSpace x‖ := by rw [norm_toSpace]
    _ ≤ euclidNorm x + Real.sqrt d / 2 := by linarith
    _ < euclidNorm x + Real.sqrt d / 2 + 1 := by linarith

/-- The integral of a constant over a cell is that constant. -/
private lemma setIntegral_const_cell (x : Site d) (c : ℝ) :
    ∫ _v in cell x, c = c := by
  rw [setIntegral_const]
  simp only [measureReal_def, CERW.Support.Occupation.volume_cell, ENNReal.toReal_one, one_smul]

/-- A constant function is integrable on a cell. -/
private lemma integrableOn_const_cell (x : Site d) (c : ℝ) :
    IntegrableOn (fun _v : EuclideanSpace ℝ (Fin d) => c) (cell x) :=
  integrableOn_const (by rw [CERW.Support.Occupation.volume_cell]; exact ENNReal.one_ne_top)

/-- On a cell, `||x|² - |v|²| ≤ (√d/2) (2|x| + √d/2)`. -/
private lemma abs_norm_sq_sub_norm_sq_le {x : Site d} {v : EuclideanSpace ℝ (Fin d)}
    (hv : v ∈ cell x) :
    |euclidNorm x ^ 2 - ‖v‖ ^ 2|
      ≤ Real.sqrt d / 2 * (2 * euclidNorm x + Real.sqrt d / 2) := by
  have ha : ‖toSpace x‖ = euclidNorm x := norm_toSpace x
  rw [← ha]
  have hdiff : ‖v - toSpace x‖ ≤ Real.sqrt d / 2 :=
    CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hv
  have hnorm_diff : |‖toSpace x‖ - ‖v‖| ≤ ‖toSpace x - v‖ := abs_norm_sub_norm_le _ _
  rw [norm_sub_rev] at hnorm_diff
  have h1 : |‖toSpace x‖ - ‖v‖| ≤ Real.sqrt d / 2 := hnorm_diff.trans hdiff
  have h2 : ‖v‖ ≤ ‖toSpace x‖ + Real.sqrt d / 2 := by
    calc ‖v‖ ≤ ‖toSpace x‖ + ‖v - toSpace x‖ :=
          norm_le_norm_add_norm_sub' v (toSpace x)
      _ ≤ ‖toSpace x‖ + Real.sqrt d / 2 := by linarith
  have hsq : |‖toSpace x‖ ^ 2 - ‖v‖ ^ 2|
      = |‖toSpace x‖ - ‖v‖| * (‖toSpace x‖ + ‖v‖) := by
    have hpos : (0:ℝ) ≤ ‖toSpace x‖ + ‖v‖ := by positivity
    rw [sq_sub_sq, abs_mul, abs_of_nonneg hpos]
    ring
  rw [hsq]
  have hle2 : ‖toSpace x‖ + ‖v‖ ≤ 2 * ‖toSpace x‖ + Real.sqrt d / 2 := by linarith
  exact mul_le_mul h1 hle2 (by linarith [norm_nonneg v, norm_nonneg (toSpace x)])
    (by positivity)

/-- The centre value and cell integral of `|v|²` differ by at most `(√d/2)(2|x|+√d/2)`. -/
private lemma abs_center_sub_setIntegral_cell_le (hd : 1 ≤ d) (x : Site d) :
    |euclidNorm x ^ 2 - ∫ v in cell x, ‖v‖ ^ 2 ∂volume|
      ≤ Real.sqrt d / 2 * (2 * euclidNorm x + Real.sqrt d / 2) := by
  have hsub : ∫ v in cell x, (euclidNorm x ^ 2 - ‖v‖ ^ 2)
      = euclidNorm x ^ 2 - ∫ v in cell x, ‖v‖ ^ 2 := by
    rw [integral_sub (integrableOn_const_cell x _) (integrableOn_norm_sq_cell hd x),
      setIntegral_const_cell]
  rw [← hsub]
  have h1 : |∫ v in cell x, (euclidNorm x ^ 2 - ‖v‖ ^ 2)|
      ≤ ∫ v in cell x, |euclidNorm x ^ 2 - ‖v‖ ^ 2| := by
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_integral_norm _
  have h2 : ∫ v in cell x, |euclidNorm x ^ 2 - ‖v‖ ^ 2|
      ≤ ∫ _v in cell x, (Real.sqrt d / 2 * (2 * euclidNorm x + Real.sqrt d / 2) : ℝ) := by
    refine setIntegral_mono_of_nonneg (fun v _ => abs_nonneg _) (fun v hv => ?_)
      (integrableOn_const_cell x _)
    exact abs_norm_sq_sub_norm_sq_le hv
  calc |∫ v in cell x, (euclidNorm x ^ 2 - ‖v‖ ^ 2)|
      ≤ ∫ v in cell x, |euclidNorm x ^ 2 - ‖v‖ ^ 2| := h1
    _ ≤ ∫ _v in cell x, (Real.sqrt d / 2 * (2 * euclidNorm x + Real.sqrt d / 2) : ℝ) := h2
    _ = Real.sqrt d / 2 * (2 * euclidNorm x + Real.sqrt d / 2) := setIntegral_const_cell x _

/-- The integral of `|v|²` over `B(0,ρ₂) \ B(0,ρ₁)` for `0 < ρ₁ ≤ ρ₂`. -/
private lemma setIntegral_norm_sq_ball_sdiff (hd : 1 ≤ d) {ρ₁ ρ₂ : ℝ}
    (h1 : 0 < ρ₁) (h12 : ρ₁ ≤ ρ₂) :
    ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ₂ \ Metric.ball 0 ρ₁, ‖v‖ ^ 2
      = d * CERW.unitBallVolume d / (d + 2) * (ρ₂ ^ (d + 2) - ρ₁ ^ (d + 2)) := by
  have h2 : 0 < ρ₂ := lt_of_lt_of_le h1 h12
  rw [setIntegral_sdiff measurableSet_ball (integrableOn_norm_sq_ball hd h2)
      (Metric.ball_subset_ball h12),
    setIntegral_norm_sq_ball hd h2, setIntegral_norm_sq_ball hd h1]
  ring

/-- The integral of `|v|²` over the annulus of half-width `√d/2` is `O(r^{d+1})`. -/
private lemma annulus_integral_bound (hd : 1 ≤ d) :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r + Real.sqrt d / 2)
          \ Metric.ball 0 (r - Real.sqrt d / 2), ‖v‖ ^ 2 ≤ C * r ^ (d + 1) := by
  set s : ℝ := Real.sqrt d / 2 with hs
  have hsnn : 0 ≤ s := by rw [hs]; exact div_nonneg (Real.sqrt_nonneg d) (by norm_num)
  set c : ℝ := (d : ℝ) * CERW.unitBallVolume d / ((d : ℝ) + 2) with hc
  have hcnn : 0 ≤ c := by
    rw [hc]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg d) (le_of_lt (CERW.unitBallVolume_pos d)))
      (by positivity)
  set C1 : ℝ := c * (2 * s * ((d : ℝ) + 2) * (1 + s) ^ (d + 1)) with hC1
  set C2 : ℝ := c * (2 * s) ^ (d + 2) with hC2
  have h2s : 0 ≤ 2 * s := by linarith
  have h1s : 0 ≤ 1 + s := by linarith
  have hC1nn : 0 ≤ C1 := by
    rw [hC1]
    exact mul_nonneg hcnn (mul_nonneg (mul_nonneg h2s (by positivity)) (pow_nonneg h1s _))
  have hC2nn : 0 ≤ C2 := by rw [hC2]; exact mul_nonneg hcnn (pow_nonneg h2s _)
  refine ⟨C1 + C2, fun r hr => ?_⟩
  have hrn : 0 ≤ r ^ (d + 1) := by positivity
  by_cases hsr : s < r
  · have h1 : 0 < r - s := by linarith
    have h12 : r - s ≤ r + s := by linarith
    rw [setIntegral_norm_sq_ball_sdiff hd h1 h12]
    have hle : (r + s) ^ (d + 2) - (r - s) ^ (d + 2)
        ≤ 2 * s * ((d : ℝ) + 2) * (1 + s) ^ (d + 1) * r ^ (d + 1) := by
      have habs := abs_pow_sub_pow_le (a := r + s) (b := r - s) (n := d + 2)
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ r + s),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ r - s),
        max_eq_left (by linarith : r - s ≤ r + s),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ r + s - (r - s))] at habs
      have hcast : ((d + 2 : ℕ) : ℝ) = (d : ℝ) + 2 := by push_cast; ring
      have hexp : d + 2 - 1 = d + 1 := by omega
      rw [hcast, hexp] at habs
      have hpow : (r + s) ^ (d + 1) ≤ ((1 + s) * r) ^ (d + 1) := by
        refine pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ r + s) ?_ _
        nlinarith
      calc (r + s) ^ (d + 2) - (r - s) ^ (d + 2)
          ≤ |(r + s) ^ (d + 2) - (r - s) ^ (d + 2)| := le_abs_self _
        _ ≤ (r + s - (r - s)) * ((d : ℝ) + 2) * (r + s) ^ (d + 1) := habs
        _ = 2 * s * ((d : ℝ) + 2) * (r + s) ^ (d + 1) := by ring
        _ ≤ 2 * s * ((d : ℝ) + 2) * ((1 + s) * r) ^ (d + 1) :=
            mul_le_mul_of_nonneg_left hpow (mul_nonneg h2s (by positivity))
        _ = 2 * s * ((d : ℝ) + 2) * (1 + s) ^ (d + 1) * r ^ (d + 1) := by
            rw [mul_pow]; ring
    calc c * ((r + s) ^ (d + 2) - (r - s) ^ (d + 2))
        ≤ c * (2 * s * ((d : ℝ) + 2) * (1 + s) ^ (d + 1) * r ^ (d + 1)) :=
          mul_le_mul_of_nonneg_left hle hcnn
      _ = C1 * r ^ (d + 1) := by rw [hC1]; ring
      _ ≤ (C1 + C2) * r ^ (d + 1) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC2nn) hrn
  · have hrs : r ≤ s := le_of_not_gt hsr
    have hzero : r - s ≤ 0 := by linarith
    rw [Metric.ball_eq_empty.mpr hzero, Set.sdiff_empty,
      setIntegral_norm_sq_ball hd (by linarith : 0 < r + s)]
    have hle : (r + s) ^ (d + 2) ≤ (2 * s) ^ (d + 2) * r ^ (d + 1) := by
      have h1 : r + s ≤ 2 * s := by linarith
      have h2 : (r + s) ^ (d + 2) ≤ (2 * s) ^ (d + 2) :=
        pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ r + s) h1 _
      have h3 : (1 : ℝ) ≤ r ^ (d + 1) := one_le_pow₀ hr
      nlinarith [h2, pow_nonneg h2s (d + 2), h3]
    calc c * (r + s) ^ (d + 2)
        ≤ c * ((2 * s) ^ (d + 2) * r ^ (d + 1)) := mul_le_mul_of_nonneg_left hle hcnn
      _ = C2 * r ^ (d + 1) := by rw [hC2]; ring
      _ ≤ (C1 + C2) * r ^ (d + 1) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC1nn) hrn

/-- The lattice sites with `|x| < r`. -/
private noncomputable def momentSites (d : ℕ) (r : ℝ) : Finset (Site d) :=
  (ballFinset d r).filter (fun x => euclidNorm x < r)

/-- A site lies in `momentSites d r` exactly when its norm is less than `r`. -/
private lemma mem_momentSites_iff {r : ℝ} {x : Site d} :
    x ∈ momentSites d r ↔ euclidNorm x < r := by
  rw [momentSites, Finset.mem_filter, LatticeProb.mem_ballFinset_iff]
  exact ⟨fun h => h.2, fun h => ⟨le_of_lt h, h⟩⟩

/-- The ball of radius `r - √d/2` is covered by the cells of the sites with `|x| < r`. -/
private lemma ball_subset_iUnion_cell {r : ℝ} :
    Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r - Real.sqrt d / 2)
      ⊆ ⋃ x ∈ momentSites d r, cell x := by
  intro v hv
  by_cases hpos : 0 < r - Real.sqrt d / 2
  · have hvlt : ‖v‖ < r - Real.sqrt d / 2 := by
      rwa [Metric.mem_ball, dist_zero_right] at hv
    refine Set.mem_iUnion₂.mpr ⟨cellCenter v, ?_, mem_cell_cellCenter v⟩
    rw [mem_momentSites_iff]
    have hcell := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell (mem_cell_cellCenter v)
    have hle : euclidNorm (cellCenter v) ≤ ‖v‖ + Real.sqrt d / 2 := by
      calc euclidNorm (cellCenter v) = ‖toSpace (cellCenter v)‖ := (norm_toSpace _).symm
        _ ≤ ‖v‖ + ‖toSpace (cellCenter v) - v‖ := norm_le_norm_add_norm_sub' _ _
        _ = ‖v‖ + ‖v - toSpace (cellCenter v)‖ := by rw [norm_sub_rev]
        _ ≤ ‖v‖ + Real.sqrt d / 2 := by linarith
    linarith
  · exfalso
    have hvlt : ‖v‖ < r - Real.sqrt d / 2 := by
      rwa [Metric.mem_ball, dist_zero_right] at hv
    have := norm_nonneg v
    linarith

/-- The cells of the sites with `|x| < r` lie in the ball of radius `r + √d/2`. -/
private lemma iUnion_cell_subset_ball {r : ℝ} :
    (⋃ x ∈ momentSites d r, cell x)
      ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r + Real.sqrt d / 2) := by
  intro v hv
  obtain ⟨x, hxF, hvx⟩ := Set.mem_iUnion₂.mp hv
  have hxlt : euclidNorm x < r := mem_momentSites_iff.mp hxF
  have hvx' := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hvx
  rw [Metric.mem_ball, dist_zero_right]
  calc ‖v‖ ≤ ‖toSpace x‖ + ‖v - toSpace x‖ := norm_le_norm_add_norm_sub' v (toSpace x)
    _ = euclidNorm x + ‖v - toSpace x‖ := by rw [norm_toSpace]
    _ ≤ euclidNorm x + Real.sqrt d / 2 := by linarith
    _ < r + Real.sqrt d / 2 := by linarith

/-- The cells' integral of `|v|²` differs from the ball integral by twice the annulus integral. -/
private lemma abs_setIntegral_iUnion_sub_ball_le (hd : 1 ≤ d) {r : ℝ} (hr : 1 ≤ r) :
    |(∫ x in (⋃ x ∈ momentSites d r, cell x), ‖x‖ ^ 2 ∂volume)
      - (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖x‖ ^ 2 ∂volume)|
    ≤ 2 * (∫ x in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r + Real.sqrt d / 2)
        \ Metric.ball 0 (r - Real.sqrt d / 2)), ‖x‖ ^ 2 ∂volume) := by
  set U : Set (EuclideanSpace ℝ (Fin d)) := ⋃ x ∈ momentSites d r, cell x with hU
  set A0 : Set (EuclideanSpace ℝ (Fin d)) := Metric.ball 0 (r - Real.sqrt d / 2) with hA0
  set Ann : Set (EuclideanSpace ℝ (Fin d)) :=
    Metric.ball 0 (r + Real.sqrt d / 2) \ Metric.ball 0 (r - Real.sqrt d / 2) with hAnn
  have hA0U : A0 ⊆ U := ball_subset_iUnion_cell
  have hUB : U ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r + Real.sqrt d / 2) :=
    iUnion_cell_subset_ball
  have hA0B : A0 ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r :=
    Metric.ball_subset_ball (by have := Real.sqrt_nonneg d; linarith)
  have hBB : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r
      ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r + Real.sqrt d / 2) :=
    Metric.ball_subset_ball (by have := Real.sqrt_nonneg d; linarith)
  have hA0meas : MeasurableSet A0 := by rw [hA0]; exact measurableSet_ball
  have hbig : IntegrableOn (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 2)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r + Real.sqrt d / 2)) :=
    integrableOn_norm_sq_ball hd (by have := Real.sqrt_nonneg d; linarith)
  have hUint : IntegrableOn (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 2) U :=
    hbig.mono_set hUB
  have hBint : IntegrableOn (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 2)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) := hbig.mono_set hBB
  have hAnnint : IntegrableOn (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 2) Ann :=
    hbig.mono_set (by rintro x ⟨hx, _⟩; exact hx)
  have hUA : U \ A0 ⊆ Ann := fun x hx => ⟨hUB hx.1, hx.2⟩
  have hBA : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r \ A0 ⊆ Ann :=
    fun x hx => ⟨hBB hx.1, hx.2⟩
  have hUeq : (∫ x in U \ A0, ‖x‖ ^ 2 ∂volume)
      = (∫ x in U, ‖x‖ ^ 2 ∂volume) - (∫ x in A0, ‖x‖ ^ 2 ∂volume) :=
    setIntegral_sdiff hA0meas hUint hA0U
  have hBeq : (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r \ A0, ‖x‖ ^ 2 ∂volume)
      = (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖x‖ ^ 2 ∂volume)
        - (∫ x in A0, ‖x‖ ^ 2 ∂volume) :=
    setIntegral_sdiff hA0meas hBint hA0B
  have hUA_le : (∫ x in U \ A0, ‖x‖ ^ 2 ∂volume)
      ≤ (∫ x in Ann, ‖x‖ ^ 2 ∂volume) :=
    setIntegral_mono_set hAnnint (ae_of_all _ (fun x => by positivity))
      (ae_of_all _ (fun x hx => hUA hx))
  have hBA_le : (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r \ A0,
        ‖x‖ ^ 2 ∂volume)
      ≤ (∫ x in Ann, ‖x‖ ^ 2 ∂volume) :=
    setIntegral_mono_set hAnnint (ae_of_all _ (fun x => by positivity))
      (ae_of_all _ (fun x hx => hBA hx))
  have hUA_nn : 0 ≤ (∫ x in U \ A0, ‖x‖ ^ 2 ∂volume) :=
    setIntegral_nonneg_of_ae (Eventually.of_forall fun x => by positivity)
  have hBA_nn : 0 ≤ (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r \ A0,
      ‖x‖ ^ 2 ∂volume) :=
    setIntegral_nonneg_of_ae (Eventually.of_forall fun x => by positivity)
  have hUB' : (∫ x in U, ‖x‖ ^ 2 ∂volume)
      = (∫ x in A0, ‖x‖ ^ 2 ∂volume) + (∫ x in U \ A0, ‖x‖ ^ 2 ∂volume) := by
    linarith [hUeq]
  have hBB' : (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖x‖ ^ 2 ∂volume)
      = (∫ x in A0, ‖x‖ ^ 2 ∂volume)
        + (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r \ A0,
            ‖x‖ ^ 2 ∂volume) := by
    linarith [hBeq]
  have hdiff : (∫ x in U, ‖x‖ ^ 2 ∂volume)
        - (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖x‖ ^ 2 ∂volume)
      = (∫ x in U \ A0, ‖x‖ ^ 2 ∂volume)
        - (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r \ A0,
            ‖x‖ ^ 2 ∂volume) := by
    rw [hUB', hBB']; ring
  rw [hdiff]
  have h1 : |(∫ x in U \ A0, ‖x‖ ^ 2 ∂volume)
      - (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r \ A0, ‖x‖ ^ 2 ∂volume)|
      ≤ |(∫ x in U \ A0, ‖x‖ ^ 2 ∂volume)|
        + |(∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r \ A0,
              ‖x‖ ^ 2 ∂volume)| := by
    have := abs_add_le (∫ x in U \ A0, ‖x‖ ^ 2 ∂volume)
      (-(∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r \ A0, ‖x‖ ^ 2 ∂volume))
    simpa [sub_eq_add_neg] using this
  have h2 : |(∫ x in U \ A0, ‖x‖ ^ 2 ∂volume)|
      + |(∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r \ A0, ‖x‖ ^ 2 ∂volume)|
      ≤ 2 * (∫ x in Ann, ‖x‖ ^ 2 ∂volume) := by
    rw [abs_of_nonneg hUA_nn, abs_of_nonneg hBA_nn]
    linarith [hUA_le, hBA_le]
  linarith [h1, h2]


/-- For `r ≥ 1` there are at most `3^d r^d` sites with `|x| < r`. -/
private lemma momentSites_card_le (r : ℝ) (hr : 1 ≤ r) :
    ((momentSites d r).card : ℝ) ≤ (3 : ℝ) ^ d * r ^ d := by
  have h1 : (momentSites d r).card ≤ (ballFinset d r).card := by
    rw [momentSites]; exact Finset.card_filter_le _ _
  have h1' : ((momentSites d r).card : ℝ) ≤ ((ballFinset d r).card : ℝ) := by
    exact_mod_cast h1
  calc ((momentSites d r).card : ℝ) ≤ ((ballFinset d r).card : ℝ) := h1'
    _ ≤ (2 * r + 1) ^ d := LatticeProb.card_ballFinset_le d (by linarith)
    _ ≤ (3 * r) ^ d := pow_le_pow_left₀ (by linarith) (by linarith) d
    _ = (3 : ℝ) ^ d * r ^ d := by rw [mul_pow]

/-- The sum of the per-cell centre errors is `O(r^{d+1})`. -/
private lemma sum_abs_center_sub_cell_le (hd : 1 ≤ d) {r : ℝ} (hr : 1 ≤ r) :
    ∑ x ∈ momentSites d r,
      |euclidNorm x ^ 2 - ∫ v in cell x, ‖v‖ ^ 2 ∂volume|
    ≤ (Real.sqrt d / 2 * (Real.sqrt d / 2 + 2) * (3 : ℝ) ^ d) * r ^ (d + 1) := by
  have hsnn : 0 ≤ Real.sqrt d / 2 := by positivity
  have hterm : ∀ x ∈ momentSites d r,
      |euclidNorm x ^ 2 - ∫ v in cell x, ‖v‖ ^ 2 ∂volume|
      ≤ (Real.sqrt d / 2 * (Real.sqrt d / 2 + 2)) * r := by
    intro x hx
    have hxr : euclidNorm x < r := mem_momentSites_iff.mp hx
    have hb := abs_center_sub_setIntegral_cell_le hd x
    calc |euclidNorm x ^ 2 - ∫ v in cell x, ‖v‖ ^ 2 ∂volume|
        ≤ Real.sqrt d / 2 * (2 * euclidNorm x + Real.sqrt d / 2) := hb
      _ ≤ Real.sqrt d / 2 * (2 * r + Real.sqrt d / 2) := by gcongr
      _ ≤ Real.sqrt d / 2 * (2 * r + Real.sqrt d / 2 * r) := by
          gcongr
          nlinarith [hsnn, hr]
      _ = (Real.sqrt d / 2 * (Real.sqrt d / 2 + 2)) * r := by ring
  calc ∑ x ∈ momentSites d r,
        |euclidNorm x ^ 2 - ∫ v in cell x, ‖v‖ ^ 2 ∂volume|
      ≤ ∑ x ∈ momentSites d r, (Real.sqrt d / 2 * (Real.sqrt d / 2 + 2)) * r :=
        Finset.sum_le_sum hterm
    _ = ((momentSites d r).card : ℝ)
          * ((Real.sqrt d / 2 * (Real.sqrt d / 2 + 2)) * r) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((3 : ℝ) ^ d * r ^ d) * ((Real.sqrt d / 2 * (Real.sqrt d / 2 + 2)) * r) :=
        mul_le_mul_of_nonneg_right (momentSites_card_le r hr) (by positivity)
    _ = (Real.sqrt d / 2 * (Real.sqrt d / 2 + 2) * (3 : ℝ) ^ d) * r ^ (d + 1) := by ring

/-- `Σ_{x ∈ ℤ^d, |x| < r} |x|² = (d ω_d/(d+2)) r^{d+2} + O(r^{d+1})` for `r ≥ 1`. -/
theorem abs_sum_norm_sq_sub_le {d : ℕ} (hd : 1 ≤ d) :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      |∑ x ∈ (ballFinset d r).filter (fun x => euclidNorm x < r), euclidNorm x ^ 2
        - d * CERW.unitBallVolume d / (d + 2) * r ^ (d + 2)| ≤ C * r ^ (d + 1) := by
  obtain ⟨Cann, hAnnb⟩ := annulus_integral_bound (d := d) hd
  refine ⟨Real.sqrt d / 2 * (Real.sqrt d / 2 + 2) * (3 : ℝ) ^ d + 2 * Cann,
    fun r hr => ?_⟩
  have hrpos : 0 < r := by linarith
  have hF : (ballFinset d r).filter (fun x => euclidNorm x < r) = momentSites d r := rfl
  rw [hF]
  have hS : ∑ x ∈ momentSites d r, euclidNorm x ^ 2
      = ∑ x ∈ momentSites d r, ‖toSpace x‖ ^ 2 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [norm_toSpace]
  have hunion : (∫ v in (⋃ x ∈ momentSites d r, cell x), ‖v‖ ^ 2 ∂volume)
      = ∑ x ∈ momentSites d r, (∫ v in cell x, ‖v‖ ^ 2 ∂volume) :=
    integral_biUnion_finset (momentSites d r)
      (fun x _ => CERW.Support.Occupation.measurableSet_cell x)
      (fun x _ y _ hxy => cell_disjoint hxy)
      (fun x _ => integrableOn_norm_sq_cell hd x)
  have hdecomp : (∑ x ∈ momentSites d r, euclidNorm x ^ 2)
        - (∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖v‖ ^ 2 ∂volume)
      = (∑ x ∈ momentSites d r,
            (‖toSpace x‖ ^ 2 - ∫ v in cell x, ‖v‖ ^ 2 ∂volume))
        + ((∫ v in (⋃ x ∈ momentSites d r, cell x), ‖v‖ ^ 2 ∂volume)
            - (∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r,
                ‖v‖ ^ 2 ∂volume)) := by
    rw [hS, Finset.sum_sub_distrib, ← hunion]
    ring
  have hT1 : |∑ x ∈ momentSites d r,
        (‖toSpace x‖ ^ 2 - ∫ v in cell x, ‖v‖ ^ 2 ∂volume)|
      ≤ (Real.sqrt d / 2 * (Real.sqrt d / 2 + 2) * (3 : ℝ) ^ d) * r ^ (d + 1) := by
    have hcongr : ∑ x ∈ momentSites d r,
          |‖toSpace x‖ ^ 2 - ∫ v in cell x, ‖v‖ ^ 2 ∂volume|
        = ∑ x ∈ momentSites d r,
          |euclidNorm x ^ 2 - ∫ v in cell x, ‖v‖ ^ 2 ∂volume| := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [norm_toSpace]
    refine (Finset.abs_sum_le_sum_abs
      (fun x => ‖toSpace x‖ ^ 2 - ∫ v in cell x, ‖v‖ ^ 2 ∂volume)
      (momentSites d r)).trans ?_
    rw [hcongr]
    exact sum_abs_center_sub_cell_le hd hr
  have hT2 : |(∫ v in (⋃ x ∈ momentSites d r, cell x), ‖v‖ ^ 2 ∂volume)
        - (∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖v‖ ^ 2 ∂volume)|
      ≤ 2 * Cann * r ^ (d + 1) := by
    calc |(∫ v in (⋃ x ∈ momentSites d r, cell x), ‖v‖ ^ 2 ∂volume)
          - (∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖v‖ ^ 2 ∂volume)|
        ≤ 2 * (∫ v in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r + Real.sqrt d / 2)
              \ Metric.ball 0 (r - Real.sqrt d / 2)), ‖v‖ ^ 2 ∂volume) :=
          abs_setIntegral_iUnion_sub_ball_le hd hr
      _ ≤ 2 * (Cann * r ^ (d + 1)) :=
          mul_le_mul_of_nonneg_left (hAnnb r hr) (by norm_num)
      _ = 2 * Cann * r ^ (d + 1) := by ring
  have hbeq : d * CERW.unitBallVolume d / (d + 2) * r ^ (d + 2)
      = ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖v‖ ^ 2 ∂volume :=
    (setIntegral_norm_sq_ball (d := d) hd hrpos).symm
  rw [hbeq, hdecomp]
  calc |(∑ x ∈ momentSites d r,
          (‖toSpace x‖ ^ 2 - ∫ v in cell x, ‖v‖ ^ 2 ∂volume))
        + ((∫ v in (⋃ x ∈ momentSites d r, cell x), ‖v‖ ^ 2 ∂volume)
            - (∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖v‖ ^ 2 ∂volume))|
      ≤ |∑ x ∈ momentSites d r,
            (‖toSpace x‖ ^ 2 - ∫ v in cell x, ‖v‖ ^ 2 ∂volume)|
        + |(∫ v in (⋃ x ∈ momentSites d r, cell x), ‖v‖ ^ 2 ∂volume)
            - (∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖v‖ ^ 2 ∂volume)| :=
        abs_add_le _ _
    _ ≤ (Real.sqrt d / 2 * (Real.sqrt d / 2 + 2) * (3 : ℝ) ^ d) * r ^ (d + 1)
          + 2 * Cann * r ^ (d + 1) := add_le_add hT1 hT2
    _ = (Real.sqrt d / 2 * (Real.sqrt d / 2 + 2) * (3 : ℝ) ^ d + 2 * Cann) * r ^ (d + 1) := by
        ring

end CERW.Generic.Lattice
