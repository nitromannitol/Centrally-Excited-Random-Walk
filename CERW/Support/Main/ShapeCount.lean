import CERW.Support.Main.GoodEvent
import CERW.Support.Main.ScaleLimits
import CERW.Support.Occupation.Facts

/-!
# The shape theorem from the fluctuation event: counts and fixed sites

If the fluctuation event `fluctGood d ε C Y n` holds for all large `n`, then
`|A_n|/N^d → ω_d a^d`. Since `V_n = A_n ∪ {X_n}`, also `|V_n|/N^d → ω_d a^d`. At a fixed
site `x`, `ℓ_n(x)/N` is within `C Q^{1/d}` of `2dε (a - |x|/N)_+`, which tends to `2dε a > 0`.
So every site is visited infinitely often.
-/

namespace CERW.Support.Main

open Filter Topology MeasureTheory LatticeProb CERW

variable {d : ℕ}

/-- The fluctuation scale `N n = n^{1/(d+1)}` tends to infinity. -/
private lemma tendsto_scale_atTop (d : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / (d + 1))) atTop atTop :=
  (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop

/-- The reciprocal `1 / N n ^ d` of the scale tends to zero. -/
private lemma tendsto_inv_scale_pow_zero {d : ℕ} (hd : d ≠ 0) :
    Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ d)
      atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop (tendsto_scale_atTop d)
  have hpow := hN.pow d
  simpa only [div_pow, one_pow, zero_pow hd] using hpow

/-- The counting, fixed-site and recurrence clauses of `thm:shape` for a path on which the
fluctuation event holds eventually. -/
theorem count_and_pointwise_of_good (hd : 2 ≤ d) {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    {Y : ℕ → Site d} (hY : ∀ᶠ n in atTop, fluctGood d ε C Y n) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let N : ℕ → ℝ := fun n => (n : ℝ) ^ ((1 : ℝ) / (d + 1))
    Tendsto (fun n => ((visitedRange Y n).card : ℝ) / N n ^ d) atTop (𝓝 (ωd * a ^ d)) ∧
    (∀ x : Site d, Tendsto (fun n => (localTime Y n x : ℝ) / N n) atTop (𝓝 (2 * d * ε * a))) ∧
    (∀ x : Site d, ∃ᶠ j in atTop, Y j = x) := by
  let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
  let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
  let N : ℕ → ℝ := fun n => (n : ℝ) ^ ((1 : ℝ) / (d + 1))
  let Q : ℕ → ℝ := fun n => if d = 2
      then (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
      else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((d : ℝ) / (2 * d - 1))
  change Tendsto (fun n => ((visitedRange Y n).card : ℝ) / N n ^ d) atTop (𝓝 (ωd * a ^ d)) ∧
    (∀ x : Site d, Tendsto (fun n => (localTime Y n x : ℝ) / N n) atTop
      (𝓝 (2 * d * ε * a))) ∧
    (∀ x : Site d, ∃ᶠ j in atTop, Y j = x)
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hωpos : 0 < ωd := by
    rw [show ωd = unitBallVolume d from rfl]
    exact unitBallVolume_pos d
  have ha_pos : 0 < a := by
    rw [show a = ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1)) from rfl]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hQ : Tendsto Q atTop (𝓝 0) := tendsto_rate_zero hd
  have hQrpow : Tendsto (fun n => Q n ^ ((1 : ℝ) / d)) atTop (𝓝 0) :=
    hQ.rpow_const_nhds_zero (one_div_pos.mpr hdR)
  have hNtop : Tendsto N atTop atTop := tendsto_scale_atTop d
  have hNinv : Tendsto (fun n => 1 / N n ^ d) atTop (𝓝 0) :=
    tendsto_inv_scale_pow_zero (by omega)
  have hvol : ∀ᶠ n in atTop,
      |((departureRange Y n).card : ℝ) / N n ^ d - ωd * a ^ d| ≤ C * Q n := by
    filter_upwards [hY] with n hn
    dsimp only [fluctGood] at hn
    have h4 := hn.2.2.2.1
    have hle : ENNReal.ofReal |((departureRange Y n).card : ℝ) / N n ^ d - ωd * a ^ d|
        ≤ ENNReal.ofReal (C * Q n) :=
      (le_add_of_nonneg_left zero_le).trans h4
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (rate_nonneg d n))).mp hle
  have hA_lim : Tendsto (fun n => ((departureRange Y n).card : ℝ) / N n ^ d) atTop
      (𝓝 (ωd * a ^ d)) := by
    have hg : Tendsto (fun n =>
        ((departureRange Y n).card : ℝ) / N n ^ d - ωd * a ^ d) atTop (𝓝 0) := by
      apply squeeze_zero_norm'
      · filter_upwards [hvol] with n hn
        simpa only [Real.norm_eq_abs] using hn
      · simpa only [mul_zero] using Filter.Tendsto.const_mul C hQ
    have hconst : Tendsto (fun _ : ℕ => ωd * a ^ d) atTop (𝓝 (ωd * a ^ d)) :=
      tendsto_const_nhds
    have hadd := hg.add hconst
    simpa only [sub_add_cancel, zero_add] using hadd
  have hA1_lim : Tendsto (fun n =>
      ((departureRange Y n).card : ℝ) / N n ^ d + 1 / N n ^ d) atTop (𝓝 (ωd * a ^ d)) := by
    have hadd := hA_lim.add hNinv
    simpa only [add_zero] using hadd
  have hV_lim : Tendsto (fun n => ((visitedRange Y n).card : ℝ) / N n ^ d) atTop
      (𝓝 (ωd * a ^ d)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hA_lim hA1_lim ?_ ?_
    · filter_upwards with n
      have hsub : departureRange Y n ⊆ visitedRange Y n := by
        rw [visitedRange_eq_insert]
        exact Finset.subset_insert _ _
      exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
        (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) d)
    · filter_upwards with n
      rw [← add_div]
      have hcard : (visitedRange Y n).card ≤ (departureRange Y n).card + 1 := by
        rw [visitedRange_eq_insert]
        exact Finset.card_insert_le _ _
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard)
        (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) d)
  have hpoint : ∀ x : Site d,
      Tendsto (fun n => (localTime Y n x : ℝ) / N n) atTop (𝓝 (2 * d * ε * a)) := by
    intro x
    have hprof : ∀ᶠ n in atTop,
        |(localTime Y n x : ℝ) / N n
          - 2 * d * ε * max (a - euclidNorm x / N n) 0| ≤ C * Q n ^ ((1 : ℝ) / d) := by
      filter_upwards [hY] with n hn
      dsimp only [fluctGood] at hn
      exact hn.2.2.2.2 x
    have hfg : Tendsto (fun n => (localTime Y n x : ℝ) / N n
        - 2 * d * ε * max (a - euclidNorm x / N n) 0) atTop (𝓝 0) := by
      apply squeeze_zero_norm'
      · filter_upwards [hprof] with n hn
        simpa only [Real.norm_eq_abs] using hn
      · simpa only [mul_zero] using Filter.Tendsto.const_mul C hQrpow
    have hg : Tendsto (fun n => 2 * d * ε * max (a - euclidNorm x / N n) 0) atTop
        (𝓝 (2 * d * ε * a)) := by
      have hdiv : Tendsto (fun n => euclidNorm x / N n) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hNtop
      have hsub : Tendsto (fun n => a - euclidNorm x / N n) atTop (𝓝 (a - 0)) :=
        tendsto_const_nhds.sub hdiv
      have hmax : Tendsto (fun n => max (a - euclidNorm x / N n) 0) atTop
          (𝓝 (max (a - 0) 0)) := hsub.max tendsto_const_nhds
      have hscaled := Filter.Tendsto.const_mul (2 * d * ε) hmax
      simpa only [sub_zero, max_eq_left ha_pos.le] using hscaled
    have hadd := hfg.add hg
    simpa only [sub_add_cancel, zero_add] using hadd
  have hrec : ∀ x : Site d, ∃ᶠ j in atTop, Y j = x := by
    intro x
    by_contra hnot
    rw [not_frequently] at hnot
    obtain ⟨m, hm⟩ := eventually_atTop.mp hnot
    have hle : ∀ n : ℕ, localTime Y n x ≤ m := by
      intro n
      rw [localTime]
      calc ((Finset.range n).filter fun j => Y j = x).card
          ≤ (Finset.range m).card := by
            apply Finset.card_le_card
            intro j hj
            rw [Finset.mem_filter] at hj
            obtain ⟨hjn, hjx⟩ := hj
            rw [Finset.mem_range] at hjn ⊢
            by_contra hjm
            exact hm j (Nat.le_of_not_lt hjm) hjx
        _ = m := Finset.card_range m
    have hzero : Tendsto (fun n => (localTime Y n x : ℝ) / N n) atTop (𝓝 0) := by
      refine squeeze_zero (g := fun n => (m : ℝ) / N n) ?_ ?_ ?_
      · intro n
        exact div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      · intro n
        exact div_le_div_of_nonneg_right (by exact_mod_cast hle n)
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      · exact tendsto_const_nhds.div_atTop hNtop
    have huniq := tendsto_nhds_unique (hpoint x) hzero
    have hpos : 0 < 2 * d * ε * a := by positivity
    linarith
  exact ⟨hV_lim, hpoint, hrec⟩

end CERW.Support.Main
