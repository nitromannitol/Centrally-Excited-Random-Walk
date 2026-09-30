import CERW.Support.Statements
import CERW.Support.Contact.Quadratic
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellVolume
import CERW.Support.Occupation.FreshSum
import CERW.Support.Occupation.Facts
import CERW.Generic.Kernel.RadialPacking
import CERW.Support.Main.ScaleLimits

/-!
# The limit laws for the sum of the distances from the origin

`CERW.Support.Limit.moment_fluctuations_of` proves Theorem 8.1 of the paper (the central limit
theorem and the law of the iterated logarithm for `Σ_{x ∈ A_n} |x|` and for the moment radius),
from the limit shape and fluctuation theorems and the cited martingale limit theorems.

The proof follows the paper. The Dynkin martingale `𝒬` of `|x|²` equals
`2ε Σ_{x ∈ A_n} |x| - n + |X_n|²`. Its bracket is
`(4/d) Σ_{t<n} |X_t|² - 4ε² Σ_{first departures} |X_t|²`, which is asymptotic to `r_n^{d+3}` times
an explicit constant by comparing the local times with the limit profile and a lattice sum with its
integral. The cited central limit theorem and law of the iterated logarithm apply to `𝒬`, and the
sum and the moment radius follow by a perturbation argument and a delta-method argument.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Limit

open CERW.Support.Statements

open LatticeProb CERW CERW.Support.Occupation CERW.Support.Law CERW.Support.Contact

/-- The profile `(r - t)₊ t²`. -/
private noncomputable def tentSq (r t : ℝ) : ℝ := max (r - t) 0 * t ^ 2

/-- The profile vanishes from `t = r` on. -/
private theorem tentSq_of_le {r t : ℝ} (h : r ≤ t) : tentSq r t = 0 := by
  rw [tentSq, max_eq_right (by linarith), zero_mul]

/-- The profile is `(r - t) t²` below `r`. -/
private theorem tentSq_of_ge {r t : ℝ} (h : t ≤ r) : tentSq r t = (r - t) * t ^ 2 := by
  rw [tentSq, max_eq_left (by linarith)]

/-- The profile is nonnegative. -/
private theorem tentSq_nonneg (r t : ℝ) : 0 ≤ tentSq r t :=
  mul_nonneg (le_max_right _ _) (sq_nonneg t)

/-- The profile is `r²`-Lipschitz on `[0, r]`. -/
private theorem abs_tentSq_sub_le_of_le {r s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hsr : s ≤ r)
    (htr : t ≤ r) : |tentSq r s - tentSq r t| ≤ r ^ 2 * |s - t| := by
  rw [tentSq_of_ge hsr, tentSq_of_ge htr]
  have h : (r - s) * s ^ 2 - (r - t) * t ^ 2 = (s - t) * (r * (s + t) - s ^ 2 - s * t - t ^ 2) := by
    ring
  rw [h, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg hs (sub_nonneg.2 hsr), mul_nonneg ht (sub_nonneg.2 htr),
      mul_nonneg hs ht, mul_nonneg (sub_nonneg.2 hsr) (sub_nonneg.2 htr)]
  · nlinarith [sq_nonneg (r - (s + t) / 2), sq_nonneg s, sq_nonneg t, sq_nonneg (s + t)]

/-- The profile is `r²`-Lipschitz on `t ≥ 0`. -/
private theorem abs_tentSq_sub_le {r s t : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |tentSq r s - tentSq r t| ≤ r ^ 2 * |s - t| := by
  rcases le_total s r with hsr | hrs <;> rcases le_total t r with htr | hrt
  · exact abs_tentSq_sub_le_of_le hs ht hsr htr
  · have h1 := abs_tentSq_sub_le_of_le hs hr hsr le_rfl
    rw [tentSq_of_le le_rfl, ← tentSq_of_le hrt] at h1
    calc |tentSq r s - tentSq r t| ≤ r ^ 2 * |s - r| := h1
      _ ≤ r ^ 2 * |s - t| := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg r)
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
  · have h1 := abs_tentSq_sub_le_of_le ht hr htr le_rfl
    rw [tentSq_of_le le_rfl, sub_zero] at h1
    rw [tentSq_of_le hrs, zero_sub, abs_neg]
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg r))
    rw [abs_of_nonpos (by linarith : t - r ≤ 0), abs_of_nonneg (by linarith : 0 ≤ s - t)]
    linarith
  · rw [tentSq_of_le hrs, tentSq_of_le hrt, sub_self, abs_zero]
    positivity

/-- `∫_{ℝ^d} (r - |v|)₊ |v|² dv = d ω_d r^{d+3}/((d+2)(d+3))`. -/
private theorem integral_tentSq_norm {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    ∫ v : EuclideanSpace ℝ (Fin d), tentSq r ‖v‖
      = d * unitBallVolume d * r ^ (d + 3) / ((d + 2) * (d + 3)) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have h1 : (fun v : EuclideanSpace ℝ (Fin d) => tentSq r ‖v‖) =
      fun v => (Set.Iio r).indicator (fun t : ℝ => (r - t) * t ^ 2) ‖v‖ := by
    funext v
    by_cases h : ‖v‖ < r
    · rw [tentSq_of_ge h.le, Set.indicator_of_mem (Set.mem_Iio.2 h)]
    · rw [tentSq_of_le (not_lt.1 h), Set.indicator_of_notMem (by simpa using h)]
  rw [h1, integral_fun_norm_addHaar volume, finrank_euclideanSpace_fin]
  have h2 : ∫ y in Set.Ioi (0 : ℝ),
        y ^ (d - 1) • (Set.Iio r).indicator (fun t : ℝ => (r - t) * t ^ 2) y
      = ∫ y in Set.Ioi (0 : ℝ),
        (Set.Iio r).indicator (fun t : ℝ => r * t ^ (d + 1) - t ^ (d + 2)) y := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y < r
    · simp only [Set.indicator_of_mem (Set.mem_Iio.mpr hy), smul_eq_mul]
      have : y ^ (d + 2) = y ^ (d - 1) * y ^ 3 := by
        rw [← pow_add]
        congr 1
        omega
      have h' : y ^ (d + 1) = y ^ (d - 1) * y ^ 2 := by
        rw [← pow_add]
        congr 1
        omega
      rw [this, h']
      ring
    · simp only [Set.indicator_of_notMem (mt Set.mem_Iio.mp hy), smul_zero]
  rw [h2, setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul, integral_pow,
    integral_pow]
  · simp only [smul_eq_mul, Measure.real, unitBallVolume]
    rw [zero_pow (by omega : d + 1 + 1 ≠ 0), zero_pow (by omega : d + 2 + 1 ≠ 0), nsmul_eq_mul]
    push_cast
    rw [show ((d : ℝ) + 1 + 1) = d + 2 by ring, show ((d : ℝ) + 2 + 1) = d + 3 by ring]
    have h3 : ((d : ℝ) + 2) ≠ 0 := by positivity
    have h4 : ((d : ℝ) + 3) ≠ 0 := by positivity
    field_simp
    ring
  · exact (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _
  · exact (continuous_pow _).intervalIntegrable _ _

/-- Every point of a cell is within `√d / 2` of the site of the cell. -/
private theorem euclidNorm_cellCenter_le {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    euclidNorm (cellCenter v) ≤ ‖v‖ + Real.sqrt d / 2 := by
  calc euclidNorm (cellCenter v) = ‖toSpace (cellCenter v)‖ := (norm_toSpace _).symm
    _ ≤ ‖v‖ + ‖toSpace (cellCenter v) - v‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ ‖v‖ + Real.sqrt d / 2 := by
      rw [norm_sub_rev]
      exact add_le_add le_rfl (norm_sub_toSpace_le_of_mem_cell (mem_cell_cellCenter v))

/-- For `r ≥ √d`, the lattice sum of the profile `(r - |x|)₊ |x|²` over the ball of radius `2r`
differs from the integral `d ω_d r^{d+3}/((d+2)(d+3))` by at most `5^d √d r^{d+2} / 2`. -/
private theorem abs_sum_tentSq_sub_le {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : Real.sqrt d ≤ r) :
    |∑ x ∈ ballFinset d (2 * r), tentSq r (euclidNorm x)
        - d * unitBallVolume d * r ^ (d + 3) / ((d + 2) * (d + 3))|
      ≤ 5 ^ d * Real.sqrt d / 2 * r ^ (d + 2) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqpos : 0 < Real.sqrt d := Real.sqrt_pos.2 hdpos
  have hsq1 : 1 ≤ Real.sqrt d := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hd
  have hrpos : 0 < r := lt_of_lt_of_le hsqpos hr
  have hr1 : 1 ≤ r := hsq1.trans hr
  set Φ : EuclideanSpace ℝ (Fin d) → ℝ := fun v => tentSq r ‖v‖ with hΦ
  have hΦc : Continuous Φ := by
    simp only [hΦ, tentSq]
    fun_prop
  have hΦlip : ∀ v w, |Φ v - Φ w| ≤ r ^ 2 * ‖v - w‖ := fun v w =>
    (abs_tentSq_sub_le hrpos.le (norm_nonneg v) (norm_nonneg w)).trans
      (mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le v w) (sq_nonneg r))
  set S : Finset (Site d) := ballFinset d (2 * r) with hS
  have hint : ∀ x ∈ S, IntegrableOn Φ (cell x) := by
    intro x hx
    refine (hΦc.continuousOn.integrableOn_compact
      (ProperSpace.isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d))
        (euclidNorm x + Real.sqrt d / 2))).mono_set ?_
    intro v hv
    rw [mem_closedBall_zero_iff]
    calc ‖v‖ ≤ ‖toSpace x‖ + ‖v - toSpace x‖ := norm_le_norm_add_norm_sub' v (toSpace x)
      _ = euclidNorm x + ‖v - toSpace x‖ := by rw [norm_toSpace]
      _ ≤ euclidNorm x + Real.sqrt d / 2 :=
        add_le_add le_rfl (norm_sub_toSpace_le_of_mem_cell hv)
  have hUmeas : MeasurableSet (⋃ x ∈ S, cell x) :=
    Finset.measurableSet_biUnion S fun x _ => measurableSet_cell x
  have hsupp : ∀ v, v ∉ (⋃ x ∈ S, cell x) → Φ v = 0 := by
    intro v hv
    by_contra h
    have hvr : ‖v‖ < r := by
      by_contra h'
      exact h (tentSq_of_le (not_lt.1 h'))
    apply hv
    refine Set.mem_iUnion₂.2 ⟨cellCenter v, ?_, mem_cell_cellCenter v⟩
    rw [hS, LatticeProb.mem_ballFinset_iff]
    have := euclidNorm_cellCenter_le v
    linarith
  have hI : ∫ v, Φ v = ∑ x ∈ S, ∫ v in cell x, Φ v := by
    rw [← setIntegral_univ, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
      (Set.subset_univ _) (fun v hv => hsupp v hv.2)]
    exact integral_biUnion_finset S (fun x _ => measurableSet_cell x)
      (fun x _ y _ hxy => cell_disjoint hxy) hint
  have hterm : ∀ x ∈ S, |Φ (toSpace x) - ∫ v in cell x, Φ v| ≤ r ^ 2 * (Real.sqrt d / 2) := by
    intro x hx
    have hconst : ∫ v in cell x, Φ (toSpace x) = Φ (toSpace x) := by
      rw [setIntegral_const]
      simp only [measureReal_def, volume_cell, ENNReal.toReal_one, one_smul]
    have hsub : Φ (toSpace x) - ∫ v in cell x, Φ v =
        ∫ v in cell x, (Φ (toSpace x) - Φ v) := by
      have hcint : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) => Φ (toSpace x)) (cell x) :=
        integrableOn_const (by rw [volume_cell]; exact ENNReal.one_ne_top)
      rw [integral_sub hcint (hint x hx), hconst]
    rw [hsub, ← Real.norm_eq_abs]
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := cell x)
      (f := fun v => Φ (toSpace x) - Φ v) (C := r ^ 2 * (Real.sqrt d / 2))
      (by rw [volume_cell]; exact ENNReal.one_lt_top) (fun v hv => by
        rw [Real.norm_eq_abs]
        calc |Φ (toSpace x) - Φ v| ≤ r ^ 2 * ‖toSpace x - v‖ := hΦlip _ _
          _ ≤ r ^ 2 * (Real.sqrt d / 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg r)
            rw [norm_sub_rev]
            exact norm_sub_toSpace_le_of_mem_cell hv)
    simpa [measureReal_def, volume_cell] using hb
  have hsum : |∑ x ∈ S, Φ (toSpace x) - ∫ v, Φ v| ≤ (S.card : ℝ) * (r ^ 2 * (Real.sqrt d / 2)) := by
    rw [hI, ← Finset.sum_sub_distrib]
    calc |∑ x ∈ S, (Φ (toSpace x) - ∫ v in cell x, Φ v)|
        ≤ ∑ x ∈ S, |Φ (toSpace x) - ∫ v in cell x, Φ v| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ S, r ^ 2 * (Real.sqrt d / 2) := Finset.sum_le_sum hterm
      _ = (S.card : ℝ) * (r ^ 2 * (Real.sqrt d / 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (S.card : ℝ) ≤ 5 ^ d * r ^ d := by
    have h1 := LatticeProb.card_ballFinset_le d (R := 2 * r) (by linarith)
    calc (S.card : ℝ) ≤ (2 * (2 * r) + 1) ^ d := h1
      _ ≤ (5 * r) ^ d := pow_le_pow_left₀ (by linarith) (by linarith) d
      _ = 5 ^ d * r ^ d := mul_pow _ _ _
  have hΦint := integral_tentSq_norm hd hrpos
  have hsumeq : ∑ x ∈ S, Φ (toSpace x) = ∑ x ∈ S, tentSq r (euclidNorm x) :=
    Finset.sum_congr rfl fun x _ => by simp only [hΦ, norm_toSpace]
  rw [← hsumeq, ← hΦint]
  calc |∑ x ∈ S, Φ (toSpace x) - ∫ v, Φ v|
      ≤ (S.card : ℝ) * (r ^ 2 * (Real.sqrt d / 2)) := hsum
    _ ≤ (5 ^ d * r ^ d) * (r ^ 2 * (Real.sqrt d / 2)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 5 ^ d * Real.sqrt d / 2 * r ^ (d + 2) := by ring

/-- The sum of `|x_t|²` over the path is the local-time weighted sum over any ball containing the
path. -/
private theorem sum_sq_eq_sum_localTime {d : ℕ} (x : ℕ → Site d) (n : ℕ) {R : ℝ}
    (hR : maxRadius x n ≤ R) :
    ∑ t ∈ Finset.range n, euclidNorm (x t) ^ 2 =
      ∑ y ∈ ballFinset d R, (localTime x n y : ℝ) * euclidNorm y ^ 2 := by
  classical
  have h1 : ∑ t ∈ Finset.range n, euclidNorm (x t) ^ 2 =
      ∑ y ∈ departureRange x n, (localTime x n y : ℝ) * euclidNorm y ^ 2 := by
    rw [Finset.sum_comp (fun y : Site d => euclidNorm y ^ 2) x]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [nsmul_eq_mul]
    rfl
  rw [h1]
  refine Finset.sum_subset (fun y hy => ?_) (fun y _ hy => ?_)
  · have := departureRange_subset_ballFinset x n hy
    rw [LatticeProb.mem_ballFinset_iff] at this ⊢
    linarith
  · rw [mem_departureRange_iff, not_lt, Nat.le_zero] at hy
    rw [hy]
    simp

/-- The first-visit sum of `|x_t|²` over the path is nonnegative and at most the sum of `|y|²`
over any ball containing the path. -/
private theorem fresh_sum_bounds {d : ℕ} (x : ℕ → Site d) (n : ℕ) {R : ℝ}
    (hR : maxRadius x n ≤ R) :
    0 ≤ ∑ t ∈ Finset.range n, (if x t ≠ 0 ∧ x t ∉ (Finset.range t).image x then
        euclidNorm (x t) ^ 2 else 0) ∧
      ∑ t ∈ Finset.range n, (if x t ≠ 0 ∧ x t ∉ (Finset.range t).image x then
        euclidNorm (x t) ^ 2 else 0) ≤ (ballFinset d R).card * R ^ 2 := by
  rw [sum_fresh_ne_zero_eq_sum_departureRange x n (fun z : Site d => euclidNorm z ^ 2)]
  refine ⟨Finset.sum_nonneg fun z _ => ?_, ?_⟩
  · split_ifs
    · exact sq_nonneg _
    · exact le_rfl
  · have hsub := departureRange_subset_ballFinset x n
    calc ∑ z ∈ departureRange x n, (if z ≠ 0 then euclidNorm z ^ 2 else 0)
        ≤ ∑ z ∈ departureRange x n, R ^ 2 := by
          refine Finset.sum_le_sum fun z hz => ?_
          have hz' : euclidNorm z ≤ R :=
            (LatticeProb.mem_ballFinset_iff.1 (hsub hz)).trans hR
          have h0 : 0 ≤ euclidNorm z := LatticeProb.euclidNorm_nonneg z
          split_ifs
          · exact pow_le_pow_left₀ h0 hz' 2
          · exact sq_nonneg R
      _ ≤ ∑ z ∈ ballFinset d R, R ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun z _ _ => sq_nonneg R
          intro z hz
          have := hsub hz
          rw [LatticeProb.mem_ballFinset_iff] at this ⊢
          linarith
      _ = (ballFinset d R).card * R ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-- A sequence whose distance to `V` is eventually at most `E₁ η + E₂ / r n` for every `η > 0`,
with `E₁ > 0` and `r n → ∞`, converges to `V`. -/
private theorem tendsto_of_eventually_le {f r : ℕ → ℝ} {V E₁ E₂ : ℝ}
    (hr : Tendsto r atTop atTop) (hE₁ : 0 < E₁)
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, |f n - V| ≤ E₁ * η + E₂ / r n) :
    Tendsto f atTop (𝓝 V) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hη : 0 < δ / (2 * E₁) := by positivity
  filter_upwards [h _ hη, hr.eventually_gt_atTop (2 * |E₂| / δ + 1)] with n h1 h2
  have h0 : 0 ≤ 2 * |E₂| / δ := by positivity
  have hrpos : 0 < r n := by linarith
  rw [Real.dist_eq]
  have h3 : E₂ / r n < δ / 2 := by
    rw [div_lt_iff₀ hrpos]
    have h4 : 2 * |E₂| / δ < r n := by linarith
    rw [div_lt_iff₀ hδ] at h4
    calc E₂ ≤ |E₂| := le_abs_self _
      _ < δ / 2 * r n := by linarith
  have h5 : E₁ * (δ / (2 * E₁)) = δ / 2 := by
    field_simp
  linarith

/-- For a path with local times close to the limit profile and confined to the ball of radius
`2 r_n`, the bracket `(4/d) Σ_{t<n} |x_t|² - 4ε² Σ_{first visits} |x_t|²` is `r_n^{d+3}` times the
limit constant, asymptotically. -/
private theorem tendsto_bracket_quotient {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {r : ℕ → ℝ}
    (hr : Tendsto r atTop atTop) (x : ℕ → Site d)
    (hloc : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ y : Site d,
      |(localTime x n y : ℝ) - 2 * d * ε * max (r n - euclidNorm y) 0| ≤ η * r n)
    (hmax : ∀ᶠ n : ℕ in atTop, maxRadius x n ≤ 2 * r n) :
    Tendsto (fun n : ℕ => ((4 / d) * ∑ t ∈ Finset.range n, euclidNorm (x t) ^ 2
        - 4 * ε ^ 2 * ∑ t ∈ Finset.range n, (if x t ≠ 0 ∧ x t ∉ (Finset.range t).image x then
            euclidNorm (x t) ^ 2 else 0)) / r n ^ (d + 3)) atTop
      (𝓝 (8 * d * ε * unitBallVolume d / ((d + 2) * (d + 3)))) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  refine tendsto_of_eventually_le (E₁ := 16 * 5 ^ d / d)
    (E₂ := 8 * ε * (5 ^ d * Real.sqrt d / 2) + 16 * ε ^ 2 * 5 ^ d) hr (by positivity)
    (fun η hη => ?_)
  filter_upwards [hloc η hη, hmax, hr.eventually_ge_atTop (max (Real.sqrt d) 1)]
    with n hl hm hrn
  have hρd : Real.sqrt d ≤ r n := (le_max_left _ _).trans hrn
  have hρ1 : 1 ≤ r n := (le_max_right _ _).trans hrn
  have hρpos : 0 < r n := by linarith
  set ρ := r n with hρ
  set B := ballFinset d (2 * ρ) with hB
  have hBcard : (B.card : ℝ) ≤ 5 ^ d * ρ ^ d := by
    have h1 := LatticeProb.card_ballFinset_le d (R := 2 * ρ) (by linarith)
    calc (B.card : ℝ) ≤ (2 * (2 * ρ) + 1) ^ d := h1
      _ ≤ (5 * ρ) ^ d := pow_le_pow_left₀ (by linarith) (by linarith) d
      _ = 5 ^ d * ρ ^ d := mul_pow _ _ _
  have hT := sum_sq_eq_sum_localTime x n hm
  obtain ⟨hF0, hF1⟩ := fresh_sum_bounds x n hm
  set T := ∑ t ∈ Finset.range n, euclidNorm (x t) ^ 2 with hTdef
  set F := ∑ t ∈ Finset.range n, (if x t ≠ 0 ∧ x t ∉ (Finset.range t).image x then
    euclidNorm (x t) ^ 2 else 0) with hFdef
  set Sp := ∑ y ∈ B, tentSq ρ (euclidNorm y) with hSp
  set M : ℝ := d * unitBallVolume d * ρ ^ (d + 3) / ((d + 2) * (d + 3)) with hM
  have hFb : F ≤ 4 * 5 ^ d * ρ ^ (d + 2) := by
    calc F ≤ (B.card : ℝ) * (2 * ρ) ^ 2 := hF1
      _ ≤ 5 ^ d * ρ ^ d * (2 * ρ) ^ 2 := mul_le_mul_of_nonneg_right hBcard (by positivity)
      _ = 4 * 5 ^ d * ρ ^ (d + 2) := by ring
  have hb : |T - 2 * d * ε * Sp| ≤ 4 * 5 ^ d * η * ρ ^ (d + 3) := by
    have hsplit : T - 2 * d * ε * Sp = ∑ y ∈ B,
        ((localTime x n y : ℝ) - 2 * d * ε * max (ρ - euclidNorm y) 0) * euclidNorm y ^ 2 := by
      rw [hT, hSp, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [tentSq]
      ring
    rw [hsplit]
    calc |∑ y ∈ B, ((localTime x n y : ℝ) - 2 * d * ε * max (ρ - euclidNorm y) 0) *
          euclidNorm y ^ 2|
        ≤ ∑ y ∈ B, |((localTime x n y : ℝ) - 2 * d * ε * max (ρ - euclidNorm y) 0) *
          euclidNorm y ^ 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _y ∈ B, η * ρ * (2 * ρ) ^ 2 := by
          refine Finset.sum_le_sum fun y hy => ?_
          rw [abs_mul, abs_of_nonneg (sq_nonneg (euclidNorm y))]
          have hy' : euclidNorm y ≤ 2 * ρ := LatticeProb.mem_ballFinset_iff.1 hy
          exact mul_le_mul (hl y)
            (pow_le_pow_left₀ (LatticeProb.euclidNorm_nonneg y) hy' 2) (sq_nonneg _)
            (by positivity)
      _ = B.card * (η * ρ * (2 * ρ) ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 5 ^ d * ρ ^ d * (η * ρ * (2 * ρ) ^ 2) :=
          mul_le_mul_of_nonneg_right hBcard (by positivity)
      _ = 4 * 5 ^ d * η * ρ ^ (d + 3) := by ring
  have hc : |Sp - M| ≤ 5 ^ d * Real.sqrt d / 2 * ρ ^ (d + 2) :=
    abs_sum_tentSq_sub_le hd hρd
  have hV : 8 * d * ε * unitBallVolume d / ((d + 2) * (d + 3)) * ρ ^ (d + 3)
      = 4 / d * (2 * d * ε * M) := by
    rw [hM]
    field_simp
    ring
  have hdecomp : (4 / d) * T - 4 * ε ^ 2 * F
      - 8 * d * ε * unitBallVolume d / ((d + 2) * (d + 3)) * ρ ^ (d + 3)
      = 4 / d * (T - 2 * d * ε * Sp) + 8 * ε * (Sp - M) - 4 * ε ^ 2 * F := by
    rw [hV]
    field_simp
    ring
  have hnum : |(4 / d) * T - 4 * ε ^ 2 * F
      - 8 * d * ε * unitBallVolume d / ((d + 2) * (d + 3)) * ρ ^ (d + 3)|
      ≤ 16 * 5 ^ d / d * η * ρ ^ (d + 3)
        + (8 * ε * (5 ^ d * Real.sqrt d / 2) + 16 * ε ^ 2 * 5 ^ d) * ρ ^ (d + 2) := by
    rw [hdecomp]
    have hFabs : |4 * ε ^ 2 * F| ≤ 16 * ε ^ 2 * 5 ^ d * ρ ^ (d + 2) := by
      rw [abs_of_nonneg (by positivity)]
      calc 4 * ε ^ 2 * F ≤ 4 * ε ^ 2 * (4 * 5 ^ d * ρ ^ (d + 2)) :=
            mul_le_mul_of_nonneg_left hFb (by positivity)
        _ = 16 * ε ^ 2 * 5 ^ d * ρ ^ (d + 2) := by ring
    have h1 : |4 / (d : ℝ) * (T - 2 * d * ε * Sp)|
        ≤ 4 / d * (4 * 5 ^ d * η * ρ ^ (d + 3)) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 / d)]
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    have h2 : |8 * ε * (Sp - M)| ≤ 8 * ε * (5 ^ d * Real.sqrt d / 2 * ρ ^ (d + 2)) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 8 * ε)]
      exact mul_le_mul_of_nonneg_left hc (by positivity)
    calc |4 / (d : ℝ) * (T - 2 * d * ε * Sp) + 8 * ε * (Sp - M) - 4 * ε ^ 2 * F|
        ≤ |4 / (d : ℝ) * (T - 2 * d * ε * Sp) + 8 * ε * (Sp - M)| + |4 * ε ^ 2 * F| :=
          abs_sub _ _
      _ ≤ |4 / (d : ℝ) * (T - 2 * d * ε * Sp)| + |8 * ε * (Sp - M)| + |4 * ε ^ 2 * F| :=
          add_le_add (abs_add_le _ _) le_rfl
      _ ≤ 4 / d * (4 * 5 ^ d * η * ρ ^ (d + 3))
          + 8 * ε * (5 ^ d * Real.sqrt d / 2 * ρ ^ (d + 2))
          + 16 * ε ^ 2 * 5 ^ d * ρ ^ (d + 2) := add_le_add (add_le_add h1 h2) hFabs
      _ = _ := by ring
  have hρ3 : 0 < ρ ^ (d + 3) := by positivity
  have hdiv : ((4 / d) * T - 4 * ε ^ 2 * F) / ρ ^ (d + 3)
      - 8 * d * ε * unitBallVolume d / ((d + 2) * (d + 3))
      = ((4 / d) * T - 4 * ε ^ 2 * F
        - 8 * d * ε * unitBallVolume d / ((d + 2) * (d + 3)) * ρ ^ (d + 3)) / ρ ^ (d + 3) := by
    field_simp
  rw [hdiv, abs_div, abs_of_pos hρ3, div_le_iff₀ hρ3]
  refine hnum.trans (le_of_eq ?_)
  field_simp
  ring

/-- The mean and second moment of the increment of the squared norm under one step of the walk:
the variance is `(4/d)|y|² - 4ε² 1{first departure} |y|²`. -/
private theorem variance_sq_increment {d : ℕ} (hd : 1 ≤ d) (ε : ℝ) (x : ℕ → Site d) (t : ℕ) :
    ∑ e ∈ unitSteps d, stepProb d ε x t e * (euclidNorm (x t + e) ^ 2 - euclidNorm (x t) ^ 2) ^ 2
      - (∑ e ∈ unitSteps d, stepProb d ε x t e * euclidNorm (x t + e) ^ 2
          - euclidNorm (x t) ^ 2) ^ 2
    = 4 / d * euclidNorm (x t) ^ 2 - 4 * ε ^ 2 *
        (if x t ≠ 0 ∧ x t ∉ (Finset.range t).image x then euclidNorm (x t) ^ 2 else 0) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set y := x t with hy
  set F : Site d → ℝ := fun z => (euclidNorm z ^ 2 - euclidNorm y ^ 2) ^ 2 with hF
  have hmean := sum_stepProb_mul ε x t (fun z : Site d => euclidNorm z ^ 2)
  have hsec := sum_stepProb_mul ε x t F
  have hpair : ∀ i : Fin d, F (y + unit i) + F (y - unit i) = 8 * ((y i : ℤ) : ℝ) ^ 2 + 2 := by
    intro i
    simp only [hF]
    rw [euclidNorm_add_unit_sq, euclidNorm_sub_unit_sq]
    ring
  have hwalk : walkOp F y = 4 * euclidNorm y ^ 2 / d + 1 := by
    rw [walkOp, nbrSum, Finset.sum_congr rfl fun i _ => hpair i, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← euclidNorm_sq_eq_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hinner : y ≠ 0 → inner ℝ (unitDir (toSpace y)) (centralDiff F y) = 4 * euclidNorm y := by
    intro hy0
    rw [inner_unitDir_centralDiff]
    have hcd : ∀ i : Fin d, ((y i : ℤ) : ℝ) * ((F (y + unit i) - F (y - unit i)) / 2)
        = 4 * ((y i : ℤ) : ℝ) ^ 2 := by
      intro i
      simp only [hF]
      rw [euclidNorm_add_unit_sq, euclidNorm_sub_unit_sq]
      ring
    rw [Finset.sum_congr rfl fun i _ => hcd i, ← Finset.mul_sum, ← euclidNorm_sq_eq_sum]
    have hne : euclidNorm y ≠ 0 := by
      intro h0
      apply hy0
      have h1 : ‖toSpace y‖ = 0 := by rw [norm_toSpace, h0]
      have h2 : toSpace y = 0 := norm_eq_zero.mp h1
      funext i
      have := congrFun (congrArg WithLp.ofLp h2) i
      simpa [toSpace_apply] using this
    field_simp
  have hmean' : ∑ e ∈ unitSteps d, stepProb d ε x t e * euclidNorm (y + e) ^ 2
      = euclidNorm y ^ 2 + 1 - (if y ≠ 0 ∧ y ∉ (Finset.range t).image x then
          ε * (2 * euclidNorm y) else 0) := by
    rw [hmean, walkOp_sq_euclidNorm hd]
    split_ifs with h
    · rw [centralDiff_sq_euclidNorm, inner_smul_right, inner_unitDir_self, norm_toSpace]
    · rfl
  have hsec' : ∑ e ∈ unitSteps d, stepProb d ε x t e * F (y + e)
      = 4 * euclidNorm y ^ 2 / d + 1 - (if y ≠ 0 ∧ y ∉ (Finset.range t).image x then
          ε * (4 * euclidNorm y) else 0) := by
    rw [hsec, hwalk]
    split_ifs with h
    · rw [hinner h.1]
    · rfl
  simp only [hF] at hsec'
  rw [hsec', hmean']
  split_ifs with h
  · field_simp
    ring
  · field_simp
    ring

/-- The conditional second moment of an increment of the Dynkin martingale of `f`: the one-step
mean square oscillation of `f` minus the square of the one-step drift. -/
private theorem condExp_sq_dynkin_succ_sub_eq {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    (hεd : ε < 1 / (d : ℝ)) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) (f : Site d → ℝ)
    (t : ℕ) :
    μ[fun ω => (dynkin ε f X (t + 1) ω - dynkin ε f X t ω) ^ 2 |
        pathFiltration hX.measurable t] =ᵐ[μ]
      fun ω => ∑ e ∈ unitSteps d,
        stepProb d ε (fun j => X j ω) t e * (f (X t ω + e) - f (X t ω)) ^ 2
          - (∑ e ∈ unitSteps d, stepProb d ε (fun j => X j ω) t e * f (X t ω + e)
            - f (X t ω)) ^ 2 := by
  set h : ((i : Finset.Iic t) → Site d) → Site d → ℝ :=
    fun p z => (f z - nextMean ε f (extendPath p) t) ^ 2 with hh
  have hsq : (fun ω => (dynkin ε f X (t + 1) ω - dynkin ε f X t ω) ^ 2) =
      fun ω => h (pastPath X t ω) (X (t + 1) ω) := by
    funext ω
    rw [dynkin_succ_sub, nextMean_pastPath]
  have hint := integrable_path_next hd hε hεd hX t h
  rw [hsq]
  filter_upwards [condExp_path_next hd hε hεd hX t h hint] with ω hω
  rw [hω]
  simp only [hh, ← nextMean_pastPath]
  have hvar := sum_mul_sub_mean_sq (unitSteps d) (fun e => stepProb d ε (fun j => X j ω) t e)
    (fun e => f (X t ω + e)) (sum_stepProb hd ε _ t) (f (X t ω))
  simp only [nextMean]
  rw [hvar]

/-- The conditional second moment of an increment of the Dynkin martingale of `|x|²` is
`(4/d)|X_t|² - 4ε² 1{first departure} |X_t|²`. -/
private theorem condExp_mul_dynkin_sq_succ_sub {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    (hεd : ε < 1 / (d : ℝ)) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) (t : ℕ) :
    μ[fun ω => (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (t + 1) ω
          - dynkin ε (fun z : Site d => euclidNorm z ^ 2) X t ω) *
        (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (t + 1) ω
          - dynkin ε (fun z : Site d => euclidNorm z ^ 2) X t ω) |
        pathFiltration hX.measurable t] =ᵐ[μ]
      fun ω => 4 / d * euclidNorm (X t ω) ^ 2 - 4 * ε ^ 2 *
        (if X t ω ≠ 0 ∧ X t ω ∉ (Finset.range t).image (fun i => X i ω) then
          euclidNorm (X t ω) ^ 2 else 0) := by
  have hmul : (fun ω => (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (t + 1) ω
          - dynkin ε (fun z : Site d => euclidNorm z ^ 2) X t ω) *
        (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (t + 1) ω
          - dynkin ε (fun z : Site d => euclidNorm z ^ 2) X t ω)) =
      fun ω => (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (t + 1) ω
          - dynkin ε (fun z : Site d => euclidNorm z ^ 2) X t ω) ^ 2 := by
    funext ω
    ring
  rw [hmul]
  filter_upwards [condExp_sq_dynkin_succ_sub_eq hd hε hεd hX
    (fun z : Site d => euclidNorm z ^ 2) t] with ω hω
  rw [hω]
  exact variance_sq_increment hd ε (fun j => X j ω) t

/-- Almost surely, for every `n` the bracket of the Dynkin martingale of `|x|²` is
`(4/d) Σ_{t<n} |X_t|² - 4ε² Σ_{t<n} 1{first departure from a nonzero site} |X_t|²`. -/
private theorem ae_predBracket_dynkin_sq {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    (hεd : ε < 1 / (d : ℝ)) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ,
      predBracket μ (pathFiltration hX.measurable) (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X)
        (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X) n ω =
      (4 / d) * ∑ t ∈ Finset.range n, euclidNorm (X t ω) ^ 2
        - 4 * ε ^ 2 * ∑ t ∈ Finset.range n,
          (if X t ω ≠ 0 ∧ X t ω ∉ (Finset.range t).image (fun i => X i ω) then
            euclidNorm (X t ω) ^ 2 else 0) := by
  have hall : ∀ᵐ ω ∂μ, ∀ t : ℕ,
      (μ[fun ω => (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (t + 1) ω
          - dynkin ε (fun z : Site d => euclidNorm z ^ 2) X t ω) *
        (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (t + 1) ω
          - dynkin ε (fun z : Site d => euclidNorm z ^ 2) X t ω) |
        pathFiltration hX.measurable t]) ω =
      4 / d * euclidNorm (X t ω) ^ 2 - 4 * ε ^ 2 *
        (if X t ω ≠ 0 ∧ X t ω ∉ (Finset.range t).image (fun i => X i ω) then
          euclidNorm (X t ω) ^ 2 else 0) :=
    ae_all_iff.2 fun t => condExp_mul_dynkin_sq_succ_sub hd hε hεd hX t
  filter_upwards [hall] with ω hω n
  simp only [predBracket, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun t _ => hω t, Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.mul_sum]

/-- If `a_n ≤ (1+δ) λ_n` eventually and `(1-δ) λ_n ≤ a_n` frequently for every `δ > 0`, and
`λ_n / L_n → c`, then the same holds with `λ_n` replaced by `c L_n`. -/
private theorem lil_rescale {a lam L : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hL : ∀ᶠ n in atTop, 0 < L n) (hlam : Tendsto (fun n => lam n / L n) atTop (𝓝 c))
    (h : ∀ δ : ℝ, 0 < δ → (∀ᶠ n in atTop, a n ≤ (1 + δ) * lam n) ∧
      (∃ᶠ n in atTop, (1 - δ) * lam n ≤ a n)) :
    ∀ δ : ℝ, 0 < δ → (∀ᶠ n in atTop, a n ≤ (c + δ) * L n) ∧
      (∃ᶠ n in atTop, (c - δ) * L n ≤ a n) := by
  intro δ' hδ'
  set δ : ℝ := δ' / (2 * (c + 1)) with hδdef
  have hc1 : 0 < c + 1 := by linarith
  have hδ : 0 < δ := by positivity
  have hδc : δ * c < δ' := by
    have : δ * (c + 1) = δ' / 2 := by rw [hδdef]; field_simp
    nlinarith
  obtain ⟨hup, hlow⟩ := h δ hδ
  constructor
  · have h1 : Tendsto (fun n => (1 + δ) * (lam n / L n)) atTop (𝓝 ((1 + δ) * c)) :=
      hlam.const_mul _
    have h2 : (1 + δ) * c < c + δ' := by nlinarith
    filter_upwards [hup, hL, h1.eventually_lt_const h2] with n hn hLn h3
    calc a n ≤ (1 + δ) * lam n := hn
      _ = (1 + δ) * (lam n / L n) * L n := by field_simp
      _ ≤ (c + δ') * L n := mul_le_mul_of_nonneg_right h3.le hLn.le
  · have h1 : Tendsto (fun n => (1 - δ) * (lam n / L n)) atTop (𝓝 ((1 - δ) * c)) :=
      hlam.const_mul _
    have h2 : c - δ' < (1 - δ) * c := by nlinarith
    have hev := (h1.eventually_const_lt h2).and hL
    refine (hlow.and_eventually hev).mono fun n ⟨hn, h3, hLn⟩ => ?_
    calc (c - δ') * L n ≤ (1 - δ) * (lam n / L n) * L n :=
          mul_le_mul_of_nonneg_right h3.le hLn.le
      _ = (1 - δ) * lam n := by field_simp
      _ ≤ a n := hn

/-- Adding a perturbation that is negligible against `L_n` preserves the upper and lower
bounds. -/
private theorem lil_add_small {a e L : ℕ → ℝ} {c : ℝ} (hL : ∀ᶠ n in atTop, 0 < L n)
    (he : Tendsto (fun n => e n / L n) atTop (𝓝 0))
    (h : ∀ δ : ℝ, 0 < δ → (∀ᶠ n in atTop, a n ≤ (c + δ) * L n) ∧
      (∃ᶠ n in atTop, (c - δ) * L n ≤ a n)) :
    ∀ δ : ℝ, 0 < δ → (∀ᶠ n in atTop, a n + e n ≤ (c + δ) * L n) ∧
      (∃ᶠ n in atTop, (c - δ) * L n ≤ a n + e n) := by
  intro δ hδ
  obtain ⟨hup, hlow⟩ := h (δ / 2) (by positivity)
  have hmem : Set.Ioo (-(δ / 2)) (δ / 2) ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hev := (he.eventually (Filter.mem_of_superset hmem fun x hx => hx)).and hL
  constructor
  · filter_upwards [hup, hev] with n hn ⟨⟨h1, h2⟩, hLn⟩
    have h3 : e n < δ / 2 * L n := by
      have := (div_lt_iff₀ hLn).1 h2
      exact this
    nlinarith
  · refine (hlow.and_eventually hev).mono fun n ⟨hn, ⟨h1, h2⟩, hLn⟩ => ?_
    have h3 : -(δ / 2) * L n < e n := by
      have := (lt_div_iff₀ hLn).1 h1
      exact this
    nlinarith

/-- If `a_n ≤ (c+δ) L_n` eventually and `(c-δ) L_n ≤ a_n` frequently for every `δ > 0`, and
`A_n → κ > 0`, then the same holds for `A_n a_n` with `κ c` in place of `c`. -/
private theorem lil_mul_seq {a A L : ℕ → ℝ} {c κ : ℝ} (hc : 0 < c) (hκ : 0 < κ)
    (hL : ∀ᶠ n in atTop, 0 < L n) (hA : Tendsto A atTop (𝓝 κ))
    (h : ∀ δ : ℝ, 0 < δ → (∀ᶠ n in atTop, a n ≤ (c + δ) * L n) ∧
      (∃ᶠ n in atTop, (c - δ) * L n ≤ a n)) :
    ∀ δ : ℝ, 0 < δ → (∀ᶠ n in atTop, A n * a n ≤ (κ * c + δ) * L n) ∧
      (∃ᶠ n in atTop, (κ * c - δ) * L n ≤ A n * a n) := by
  intro δ hδ
  set t : ℝ := min (min (min 1 c) κ) (δ / (κ + c + 1)) with ht
  have htpos : 0 < t := lt_min (lt_min (lt_min one_pos hc) hκ) (by positivity)
  have ht1 : t ≤ 1 := ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _)
  have htc : t ≤ c := ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
  have htκ : t ≤ κ := (min_le_left _ _).trans (min_le_right _ _)
  have htδ : t * (κ + c + 1) ≤ δ := by
    have : t ≤ δ / (κ + c + 1) := min_le_right _ _
    calc t * (κ + c + 1) ≤ δ / (κ + c + 1) * (κ + c + 1) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = δ := by field_simp
  have htt : t * t ≤ t * 1 := mul_le_mul_of_nonneg_left ht1 htpos.le
  obtain ⟨hup, hlow⟩ := h t htpos
  have hAev : ∀ᶠ n in atTop, κ - t < A n ∧ A n < κ + t :=
    (hA.eventually (Ioo_mem_nhds (by linarith) (by linarith)))
  constructor
  · filter_upwards [hup, hAev, hL] with n hn ⟨hA1, hA2⟩ hLn
    have hApos : 0 < A n := by linarith
    have h1 : A n * a n ≤ A n * ((c + t) * L n) := mul_le_mul_of_nonneg_left hn hApos.le
    have h2 : A n * ((c + t) * L n) ≤ (κ + t) * ((c + t) * L n) :=
      mul_le_mul_of_nonneg_right hA2.le (by positivity)
    have h3 : (κ + t) * (c + t) ≤ κ * c + δ := by nlinarith
    calc A n * a n ≤ (κ + t) * ((c + t) * L n) := h1.trans h2
      _ = (κ + t) * (c + t) * L n := by ring
      _ ≤ (κ * c + δ) * L n := mul_le_mul_of_nonneg_right h3 hLn.le
  · refine (hlow.and_eventually (hAev.and hL)).mono fun n ⟨hn, ⟨hA1, hA2⟩, hLn⟩ => ?_
    have hApos : 0 < A n := by linarith
    have h1 : A n * ((c - t) * L n) ≤ A n * a n := mul_le_mul_of_nonneg_left hn hApos.le
    have h2 : (κ - t) * ((c - t) * L n) ≤ A n * ((c - t) * L n) :=
      mul_le_mul_of_nonneg_right hA1.le (mul_nonneg (by linarith) hLn.le)
    have h3 : κ * c - δ ≤ (κ - t) * (c - t) := by nlinarith
    calc (κ * c - δ) * L n ≤ (κ - t) * (c - t) * L n :=
          mul_le_mul_of_nonneg_right h3 hLn.le
      _ = (κ - t) * ((c - t) * L n) := by ring
      _ ≤ A n * a n := h2.trans h1

/-- If `P_n / s_n² → V > 0` and `log (s_n²) / log n → κ > 0`, then
`log log P_n / log log n → 1`. -/
private theorem tendsto_loglog_ratio {P s : ℕ → ℝ} {V κ : ℝ} (hV : 0 < V) (hκ : 0 < κ)
    (hs : ∀ n, 0 < s n) (hP : Tendsto (fun n => P n / s n ^ 2) atTop (𝓝 V))
    (hlog : Tendsto (fun n : ℕ => Real.log (s n ^ 2) / Real.log n) atTop (𝓝 κ)) :
    Tendsto (fun n : ℕ => Real.log (Real.log (P n)) / Real.log (Real.log n)) atTop (𝓝 1) := by
  have hlogn : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglogn : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hlogn
  have hlogV : Tendsto (fun n => Real.log (P n / s n ^ 2)) atTop (𝓝 (Real.log V)) :=
    ((Real.continuousAt_log hV.ne').tendsto).comp hP
  have hPpos : ∀ᶠ n in atTop, 0 < P n := by
    filter_upwards [hP.eventually (lt_mem_nhds hV)] with n hn
    have h2 : 0 < s n ^ 2 := pow_pos (hs n) 2
    have := (lt_div_iff₀ h2).1 hn
    linarith
  set g : ℕ → ℝ := fun n => Real.log (P n) / Real.log n with hg
  have hg_lim : Tendsto g atTop (𝓝 κ) := by
    have h1 : Tendsto (fun n : ℕ => Real.log (P n / s n ^ 2) / Real.log n) atTop (𝓝 0) :=
      hlogV.div_atTop hlogn
    have h2 := h1.add hlog
    rw [zero_add] at h2
    refine h2.congr' ?_
    filter_upwards [hPpos] with n hn
    have hsn : 0 < s n ^ 2 := pow_pos (hs n) 2
    rw [hg]
    simp only
    rw [← add_div, Real.log_div hn.ne' hsn.ne']
    ring_nf
  have hlogκ : Tendsto (fun n => Real.log (g n)) atTop (𝓝 (Real.log κ)) :=
    ((Real.continuousAt_log hκ.ne').tendsto).comp hg_lim
  have h3 : Tendsto (fun n : ℕ => Real.log (g n) / Real.log (Real.log n)) atTop (𝓝 0) :=
    hlogκ.div_atTop hloglogn
  have h4 := h3.add_const 1
  rw [zero_add] at h4
  refine h4.congr' ?_
  filter_upwards [hg_lim.eventually (lt_mem_nhds hκ), hlogn.eventually_gt_atTop 1,
    hloglogn.eventually_gt_atTop 0] with n hgn hln hlln
  have hlnpos : 0 < Real.log n := by linarith
  have hgpos : 0 < g n := hgn
  have hlogP : Real.log (P n) = g n * Real.log n := by
    rw [hg]
    simp only
    field_simp
  rw [hlogP, Real.log_mul hgpos.ne' hlnpos.ne']
  field_simp

/-- The increment-bound condition of Stout's theorem, for deterministic sequences: if `P_n / s_n²`
tends to `V > 0`, and `B_n² / s_n → 0`, then `B_n √(log log (P_n ∨ e^e)) / √P_n → 0`. -/
private theorem tendsto_stout_condition {P B s : ℕ → ℝ} {V : ℝ} (hV : 0 < V)
    (hs : ∀ n, 0 < s n) (hs' : Tendsto s atTop atTop) (hB0 : ∀ n, 0 ≤ B n)
    (hP : Tendsto (fun n => P n / s n ^ 2) atTop (𝓝 V))
    (hBs : Tendsto (fun n => B n ^ 2 / s n) atTop (𝓝 0)) :
    Tendsto (fun n => B n * Real.sqrt (Real.log (Real.log (max (P n) (Real.exp (Real.exp 1))))) /
      Real.sqrt (P n)) atTop (𝓝 0) := by
  set K : ℝ := 2 * V + Real.exp (Real.exp 1) with hK
  have hKpos : 0 < K := by positivity
  set C : ℝ := 4 * Real.sqrt K / V with hC
  have hmain : ∀ᶠ n in atTop, B n * Real.sqrt (Real.log (Real.log (max (P n)
      (Real.exp (Real.exp 1))))) / Real.sqrt (P n) ≤ Real.sqrt (C * (B n ^ 2 / s n)) := by
    filter_upwards [hP.eventually (lt_mem_nhds (half_lt_self hV)),
      hP.eventually (gt_mem_nhds (by linarith : V < 2 * V)), hs'.eventually_gt_atTop 1]
      with n h1 h2 h3
    have hsn := hs n
    have hs2 : 0 < s n ^ 2 := pow_pos hsn 2
    have hPlow : V / 2 * s n ^ 2 < P n := by
      have := (lt_div_iff₀ hs2).1 h1
      linarith
    have hPup : P n < 2 * V * s n ^ 2 := by
      have := (div_lt_iff₀ hs2).1 h2
      linarith
    have hPpos : 0 < P n := lt_trans (by positivity) hPlow
    set P' := max (P n) (Real.exp (Real.exp 1)) with hP'
    have hP'pos : 0 < P' := lt_of_lt_of_le hPpos (le_max_left _ _)
    have hlog1 : Real.exp 1 ≤ Real.log P' := by
      calc Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := (Real.log_exp _).symm
        _ ≤ Real.log P' := Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
    have hexp1 : 1 ≤ Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    have hlogpos : 0 < Real.log P' := by linarith
    have hLL : 0 ≤ Real.log (Real.log P') := Real.log_nonneg (by linarith)
    have hLLle : Real.log (Real.log P') ≤ Real.log P' := by
      have := Real.log_le_sub_one_of_pos hlogpos
      linarith
    have hlog2 : Real.log P' ≤ 2 * Real.sqrt P' := by
      have h1' : Real.log (Real.sqrt P') = Real.log P' / 2 := Real.log_sqrt hP'pos.le
      have h2' : Real.log (Real.sqrt P') ≤ Real.sqrt P' - 1 :=
        Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hP'pos)
      linarith
    have hP'le : P' ≤ K * s n ^ 2 := by
      refine max_le ?_ ?_
      · have : 2 * V * s n ^ 2 ≤ K * s n ^ 2 :=
          mul_le_mul_of_nonneg_right (by rw [hK]; linarith [Real.exp_pos (Real.exp 1)]) hs2.le
        linarith
      · have h1s : 1 ≤ s n ^ 2 := by nlinarith
        have : Real.exp (Real.exp 1) ≤ K := by rw [hK]; linarith
        nlinarith
    have hsqrtP' : Real.sqrt P' ≤ Real.sqrt K * s n := by
      calc Real.sqrt P' ≤ Real.sqrt (K * s n ^ 2) := Real.sqrt_le_sqrt hP'le
        _ = Real.sqrt K * s n := by
          rw [Real.sqrt_mul hKpos.le, Real.sqrt_sq hsn.le]
    have hLLs : Real.log (Real.log P') ≤ 2 * Real.sqrt K * s n := by
      nlinarith
    have hx2 : (B n * Real.sqrt (Real.log (Real.log P')) / Real.sqrt (P n)) ^ 2
        = B n ^ 2 * Real.log (Real.log P') / P n := by
      rw [div_pow, mul_pow, Real.sq_sqrt hLL, Real.sq_sqrt hPpos.le]
    have hx2le : (B n * Real.sqrt (Real.log (Real.log P')) / Real.sqrt (P n)) ^ 2
        ≤ C * (B n ^ 2 / s n) := by
      rw [hx2]
      have hnum : B n ^ 2 * Real.log (Real.log P') ≤ B n ^ 2 * (2 * Real.sqrt K * s n) :=
        mul_le_mul_of_nonneg_left hLLs (sq_nonneg _)
      calc B n ^ 2 * Real.log (Real.log P') / P n
          ≤ B n ^ 2 * (2 * Real.sqrt K * s n) / P n :=
            div_le_div_of_nonneg_right hnum hPpos.le
        _ ≤ B n ^ 2 * (2 * Real.sqrt K * s n) / (V / 2 * s n ^ 2) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hPlow.le
        _ = C * (B n ^ 2 / s n) := by
            rw [hC]
            field_simp
            ring
    exact (le_abs_self _).trans (Real.abs_le_sqrt hx2le)
  have hg : Tendsto (fun n => Real.sqrt (C * (B n ^ 2 / s n))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => C * (B n ^ 2 / s n)) atTop (𝓝 0) := by
      simpa using hBs.const_mul C
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at h2
    exact h2
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => ?_) hmain hg
  exact div_nonneg (mul_nonneg (hB0 n) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

/-- The bracket of a martingale is almost everywhere strongly measurable. -/
private theorem aestronglyMeasurable_predBracket {Ω : Type*} [m0 : MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (n : ℕ) :
    AEStronglyMeasurable (predBracket μ ℱ M M n) μ := by
  unfold predBracket
  refine Finset.aestronglyMeasurable_sum _ fun t _ => ?_
  exact ((stronglyMeasurable_condExp (m := ℱ t)).mono (ℱ.le t)).aestronglyMeasurable

/-- The conditional Lindeberg sum tends to zero in measure when the increment bounds are
predictable and eventually negligible against the normalization. -/
private theorem tendstoInMeasure_lindeberg {Ω : Type*} [m0 : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ)
    (hL2 : ∀ n, MemLp (M n) 2 μ)
    (B : ℕ → Ω → ℝ) (hBm : ∀ n, StronglyMeasurable[ℱ n] (B (n + 1)))
    (hBb : ∀ᵐ ω ∂μ, ∀ n, |M (n + 1) ω - M n ω| ≤ B (n + 1) ω)
    (hBbd : ∀ n, ∃ C, ∀ᵐ ω ∂μ, |B n ω| ≤ C)
    {s : ℕ → ℝ} (hs : ∀ n, 0 < s n)
    (hBmax : ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ i < n, B (i + 1) ω ≤ δ * s n)
    (δ : ℝ) (hδ : 0 < δ) :
    TendstoInMeasure μ
      (fun n => ∑ i ∈ Finset.range n,
        μ[fun ω => ((M (i + 1) ω - M i ω) / s n) ^ 2 *
          (if δ < |M (i + 1) ω - M i ω| / s n then 1 else 0) | ℱ i])
      atTop (fun _ => 0) := by
  set g : ℕ → ℕ → Ω → ℝ := fun n i ω => ((M (i + 1) ω - M i ω) / s n) ^ 2 *
    (if δ < |M (i + 1) ω - M i ω| / s n then 1 else 0) with hg
  set Φ : ℕ → ℝ → ℝ := fun n x => (x / s n) ^ 2 * (if δ * s n < x then 1 else 0) with hΦ
  have hΦm : ∀ n, Measurable (Φ n) := fun n => by
    simp only [hΦ]
    exact (measurable_id.div_const _).pow_const 2 |>.mul
      (Measurable.ite measurableSet_Ioi measurable_const measurable_const)
  have hΦnn : ∀ n x, 0 ≤ Φ n x := fun n x => by
    simp only [hΦ]
    split_ifs
    · positivity
    · simp
  -- pointwise bound of the truncated square by the predictable quantity
  have hgk : ∀ n i, ∀ᵐ ω ∂μ, g n i ω ≤ Φ n (B (i + 1) ω) := by
    intro n i
    filter_upwards [hBb] with ω hω
    have hb := hω i
    by_cases hc : δ < |M (i + 1) ω - M i ω| / s n
    · have hc' : δ * s n < B (i + 1) ω := by
        have := (lt_div_iff₀ (hs n)).1 hc
        linarith
      have habs : (M (i + 1) ω - M i ω) ^ 2 ≤ B (i + 1) ω ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      simp only [hg, hΦ]
      rw [if_pos hc, if_pos hc', mul_one, mul_one, div_pow, div_pow]
      exact div_le_div_of_nonneg_right habs (sq_nonneg _)
    · have h0 : g n i ω = 0 := by
        simp only [hg]
        rw [if_neg hc, mul_zero]
      rw [h0]
      exact hΦnn n _
  have hψm : ∀ n, Measurable (fun x : ℝ => if δ < |x| / s n then (1 : ℝ) else 0) := fun n =>
    Measurable.ite (measurableSet_lt measurable_const (measurable_id.abs.div_const _))
      measurable_const measurable_const
  have hgint : ∀ n i, Integrable (g n i) μ := by
    intro n i
    have hΔ : MemLp (fun ω => M (i + 1) ω - M i ω) 2 μ := (hL2 (i + 1)).sub (hL2 i)
    have hsq : Integrable (fun ω => ((M (i + 1) ω - M i ω) / s n) ^ 2) μ := by
      simp_rw [div_pow]
      exact hΔ.integrable_sq.div_const _
    refine hsq.mono' ?_ ?_
    · have h1 : AEStronglyMeasurable (fun ω => ((M (i + 1) ω - M i ω) / s n) ^ 2) μ :=
        hsq.aestronglyMeasurable
      have h2 : AEStronglyMeasurable
          (fun ω => if δ < |M (i + 1) ω - M i ω| / s n then (1 : ℝ) else 0) μ :=
        ((hψm n).comp_aemeasurable hΔ.aemeasurable).aestronglyMeasurable
      exact h1.mul h2
    · refine Filter.Eventually.of_forall fun ω => ?_
      simp only [hg]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
      have : |if δ < |M (i + 1) ω - M i ω| / s n then (1 : ℝ) else 0| ≤ 1 := by
        split_ifs <;> simp
      calc ((M (i + 1) ω - M i ω) / s n) ^ 2 *
            |if δ < |M (i + 1) ω - M i ω| / s n then (1 : ℝ) else 0|
          ≤ ((M (i + 1) ω - M i ω) / s n) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left this (sq_nonneg _)
        _ = ((M (i + 1) ω - M i ω) / s n) ^ 2 := mul_one _
  have hkmeas : ∀ n i, StronglyMeasurable[ℱ i] (fun ω => Φ n (B (i + 1) ω)) := fun n i =>
    ((hΦm n).comp (hBm i).measurable).stronglyMeasurable
  have hkint : ∀ n i, Integrable (fun ω => Φ n (B (i + 1) ω)) μ := by
    intro n i
    obtain ⟨C, hC⟩ := hBbd (i + 1)
    refine Integrable.of_bound ((hkmeas n i).mono (ℱ.le i)).aestronglyMeasurable ((C / s n) ^ 2) ?_
    filter_upwards [hC] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hΦnn n _)]
    have h1 : Φ n (B (i + 1) ω) ≤ (B (i + 1) ω / s n) ^ 2 := by
      simp only [hΦ]
      split_ifs
      · rw [mul_one]
      · rw [mul_zero]
        exact sq_nonneg _
    refine h1.trans ?_
    rw [← sq_abs, abs_div, abs_of_pos (hs n)]
    exact pow_le_pow_left₀ (div_nonneg (abs_nonneg _) (hs n).le)
      (div_le_div_of_nonneg_right hω (hs n).le) 2
  have hcond : ∀ n i, μ[g n i | ℱ i] ≤ᵐ[μ] fun ω => Φ n (B (i + 1) ω) := by
    intro n i
    have h1 := condExp_mono (m := ℱ i) (hgint n i) (hkint n i) (hgk n i)
    have h2 := condExp_of_stronglyMeasurable (ℱ.le i) (hkmeas n i) (hkint n i)
    rw [h2] at h1
    exact h1
  have hg0 : ∀ n i ω, 0 ≤ g n i ω := fun n i ω => by
    simp only [hg]
    split_ifs
    · positivity
    · simp
  have hnn : ∀ n i, 0 ≤ᵐ[μ] μ[g n i | ℱ i] := fun n i =>
    condExp_nonneg (Filter.Eventually.of_forall (hg0 n i))
  refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
  · exact Finset.aestronglyMeasurable_sum _ fun i _ =>
      ((stronglyMeasurable_condExp (m := ℱ i)).mono (ℱ.le i)).aestronglyMeasurable
  · have hall : ∀ᵐ ω ∂μ, ∀ n i, 0 ≤ μ[g n i | ℱ i] ω ∧
        μ[g n i | ℱ i] ω ≤ Φ n (B (i + 1) ω) :=
      ae_all_iff.2 fun n => ae_all_iff.2 fun i => by
        filter_upwards [hnn n i, hcond n i] with ω h1 h2 using ⟨h1, h2⟩
    filter_upwards [hall, hBmax] with ω hω hBω
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hBω δ hδ] with n hn
    simp only [Finset.sum_apply]
    refine (Finset.sum_eq_zero fun i hi => ?_).symm
    have hi' := Finset.mem_range.1 hi
    have h1 := (hω n i).2
    have h2 := (hω n i).1
    have h3 : Φ n (B (i + 1) ω) = 0 := by
      simp only [hΦ]
      rw [if_neg (not_lt.2 (hn i hi')), mul_zero]
    linarith


/-- The central limit theorem for a martingale with predictable increment bounds that are
eventually negligible against the normalization, and whose bracket over `s_n²` tends to `V`
almost surely. -/
private theorem clt_normalized (hCLT : MartingaleCLT.{u}) {Ω : Type u}
    [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    (M : ℕ → Ω → ℝ) (hM : Martingale M ℱ μ) (hL2 : ∀ n, MemLp (M n) 2 μ)
    (hM0 : ∀ ω, M 0 ω = 0) (B : ℕ → Ω → ℝ) (hBm : ∀ n, StronglyMeasurable[ℱ n] (B (n + 1)))
    (hBb : ∀ᵐ ω ∂μ, ∀ n, |M (n + 1) ω - M n ω| ≤ B (n + 1) ω)
    (hBbd : ∀ n, ∃ C, ∀ᵐ ω ∂μ, |B n ω| ≤ C) {s : ℕ → ℝ} (hs : ∀ n, 0 < s n) {V : ℝ}
    (hV : 0 ≤ V)
    (hBmax : ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ i < n, B (i + 1) ω ≤ δ * s n)
    (hbr : ∀ᵐ ω ∂μ,
      Tendsto (fun n => predBracket μ ℱ M M n ω / s n ^ 2) atTop (𝓝 V)) :
    TendstoInDistribution (fun n ω => M n ω / s n) atTop id (fun _ => μ)
      (gaussianReal 0 V.toNNReal) := by
  have hbrm : TendstoInMeasure μ (fun n => fun ω => predBracket μ ℱ M M n ω / s n ^ 2) atTop
      (fun _ => ((V.toNNReal : ℝ≥0) : ℝ)) := by
    rw [Real.coe_toNNReal V hV]
    refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) hbr
    simpa only [div_eq_mul_inv] using
      (aestronglyMeasurable_predBracket μ ℱ M n).mul_const ((s n ^ 2)⁻¹)
  exact hCLT μ ℱ M hM hL2 hM0 s hs V.toNNReal
    (fun δ hδ => tendstoInMeasure_lindeberg μ ℱ M hL2 B hBm hBb hBbd hs hBmax δ hδ) hbrm

/-- The law of the iterated logarithm for a martingale with predictable increment bound and
bracket `~ V s_n²`, stated for `M_n / s_n` against `√(2 log log n)`. -/
private theorem lil_normalized (hLIL : StoutLIL.{u}) {Ω : Type u} [m0 : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ)
    (hM : Martingale M ℱ μ) (hL2 : ∀ n, MemLp (M n) 2 μ) (hM0 : ∀ ω, M 0 ω = 0)
    (B : ℕ → Ω → ℝ) (hB0 : ∀ n ω, 0 ≤ B n ω) (hBm : ∀ n, StronglyMeasurable[ℱ n] (B (n + 1)))
    (hBb : ∀ᵐ ω ∂μ, ∀ n, |M (n + 1) ω - M n ω| ≤ B (n + 1) ω)
    {s : ℕ → ℝ} (hs : ∀ n, 0 < s n) (hs' : Tendsto s atTop atTop) {V κ : ℝ} (hV : 0 < V)
    (hκ : 0 < κ)
    (hbr : ∀ᵐ ω ∂μ,
      Tendsto (fun n => predBracket μ ℱ M M n ω / s n ^ 2) atTop (𝓝 V))
    (hBs : ∀ᵐ ω ∂μ, Tendsto (fun n => B n ω ^ 2 / s n) atTop (𝓝 0))
    (hlog : Tendsto (fun n : ℕ => Real.log (s n ^ 2) / Real.log n) atTop (𝓝 κ)) :
    ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ →
      (∀ᶠ n : ℕ in atTop,
        M n ω / s n ≤ (Real.sqrt V + δ) * Real.sqrt (2 * Real.log (Real.log n))) ∧
      (∃ᶠ n : ℕ in atTop,
        (Real.sqrt V - δ) * Real.sqrt (2 * Real.log (Real.log n)) ≤ M n ω / s n) := by
  have hs2 : Tendsto (fun n => s n ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp hs'
  have hinf : ∀ᵐ ω ∂μ, Tendsto (fun n => predBracket μ ℱ M M n ω) atTop atTop := by
    filter_upwards [hbr] with ω hω
    refine (hω.pos_mul_atTop hV hs2).congr fun n => ?_
    have : s n ^ 2 ≠ 0 := (pow_pos (hs n) 2).ne'
    have hsn : s n ≠ 0 := (hs n).ne'
    field_simp
  have hBcond : ∀ᵐ ω ∂μ, Tendsto (fun n => B n ω *
      Real.sqrt (Real.log (Real.log (max (predBracket μ ℱ M M n ω)
        (Real.exp (Real.exp 1))))) / Real.sqrt (predBracket μ ℱ M M n ω)) atTop (𝓝 0) := by
    filter_upwards [hbr, hBs] with ω h1 h2
    exact tendsto_stout_condition hV hs hs' (fun n => hB0 n ω) h1 h2
  have hstout := hLIL μ ℱ M hM hL2 hM0 B hBm hBb hinf hBcond
  filter_upwards [hstout, hbr] with ω hS hP
  set P : ℕ → ℝ := fun n => predBracket μ ℱ M M n ω with hPdef
  have hloglog := tendsto_loglog_ratio hV hκ hs hP hlog
  have hlogn : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglogn : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hlogn
  set L : ℕ → ℝ := fun n => Real.sqrt (2 * Real.log (Real.log n)) with hLdef
  set lam : ℕ → ℝ := fun n => Real.sqrt (2 * P n * Real.log (Real.log (P n))) / s n with hlamdef
  have hL : ∀ᶠ n in atTop, 0 < L n := by
    filter_upwards [hloglogn.eventually_gt_atTop 0] with n hn
    exact Real.sqrt_pos.2 (by linarith)
  have hlam : Tendsto (fun n => lam n / L n) atTop (𝓝 (Real.sqrt V)) := by
    have h1 : Tendsto (fun n => P n / s n ^ 2 *
        (Real.log (Real.log (P n)) / Real.log (Real.log n))) atTop (𝓝 (V * 1)) :=
      hP.mul hloglog
    have h2 := h1.sqrt
    rw [mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [hloglogn.eventually_gt_atTop 0] with n hn
    have hsn := hs n
    have hB : (0 : ℝ) ≤ 2 * Real.log (Real.log n) := by linarith
    have hBpos : 0 < 2 * Real.log (Real.log n) := by linarith
    have e1 : P n / s n ^ 2 * (Real.log (Real.log (P n)) / Real.log (Real.log n))
        = (2 * P n * Real.log (Real.log (P n))) / (s n ^ 2 * (2 * Real.log (Real.log n))) := by
      field_simp
    rw [e1, Real.sqrt_div' _ (by positivity), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hsn.le]
    simp only [hlamdef, hLdef]
    rw [div_div]
  intro δ hδ
  have hmain := lil_rescale (a := fun n => M n ω / s n) (lam := lam) (L := L)
    (Real.sqrt_nonneg V) hL hlam (fun δ hδ => ?_) δ hδ
  · exact hmain
  · obtain ⟨hup, hlow⟩ := hS δ hδ
    constructor
    · filter_upwards [hup] with n hn
      simp only [hlamdef]
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hn (hs n).le
    · refine hlow.mono fun n hn => ?_
      simp only [hlamdef]
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hn (hs n).le

/-- The normalization `s_n = r_n^{(d+3)/2}`, replaced by `1` at `n = 0` so that it is positive. -/
private noncomputable def norming (d : ℕ) (r : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 1 else r n ^ (((d : ℝ) + 3) / 2)

/-- The scale `a n^{1/(d+1)}` is positive for `n ≥ 1`. -/
private theorem scale_pos {d : ℕ} {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) {n : ℕ} (hn : n ≠ 0) : 0 < r n := by
  rw [hr n]
  exact mul_pos ha (Real.rpow_pos_of_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)) _)

/-- The scale tends to infinity. -/
private theorem tendsto_scale_atTop {d : ℕ} {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) : Tendsto r atTop atTop := by
  have h1 : Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / (d + 1))) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have h2 := (h1.comp tendsto_natCast_atTop_atTop).const_mul_atTop ha
  exact h2.congr fun n => (hr n).symm

/-- The normalization is positive. -/
private theorem norming_pos {d : ℕ} {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) (n : ℕ) : 0 < norming d r n := by
  unfold norming
  split_ifs with h
  · exact one_pos
  · exact Real.rpow_pos_of_pos (scale_pos ha hr h) _

/-- The normalization tends to infinity. -/
private theorem tendsto_norming_atTop {d : ℕ} {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) :
    Tendsto (norming d r) atTop atTop := by
  have h1 : Tendsto (fun x : ℝ => x ^ (((d : ℝ) + 3) / 2)) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have h2 := h1.comp (tendsto_scale_atTop ha hr)
  refine h2.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp [norming, hn]

/-- For `d ≥ 2`, `r_n² / s_n → 0`. -/
private theorem tendsto_scale_sq_div {d : ℕ} (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) :
    Tendsto (fun n => r n ^ 2 / norming d r n) atTop (𝓝 0) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : Tendsto (fun x : ℝ => x ^ (-(((d : ℝ) - 1) / 2))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have h2 := h1.comp (tendsto_scale_atTop ha hr)
  refine h2.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hrpos := scale_pos ha hr hn
  simp only [Function.comp, norming, if_neg hn]
  rw [← Real.rpow_natCast, ← Real.rpow_sub hrpos]
  congr 1
  push_cast
  ring

/-- For `d ≥ 2`, `r_n / s_n → 0`. -/
private theorem tendsto_scale_div {d : ℕ} (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) :
    Tendsto (fun n => r n / norming d r n) atTop (𝓝 0) := by
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => ?_) ?_
    (tendsto_scale_sq_div hd ha hr)
  · exact div_nonneg (by rw [hr n]; positivity) (norming_pos ha hr n).le
  · filter_upwards [(tendsto_scale_atTop ha hr).eventually_ge_atTop 1] with n hn
    exact div_le_div_of_nonneg_right (by nlinarith) (norming_pos ha hr n).le

/-- The square of the normalization is `r_n^{d+3}`, for `n ≥ 1`. -/
private theorem norming_sq {d : ℕ} {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) {n : ℕ} (hn : n ≠ 0) :
    norming d r n ^ 2 = r n ^ (d + 3) := by
  have hrpos := scale_pos ha hr hn
  simp only [norming, if_neg hn]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hrpos.le, ← Real.rpow_natCast]
  congr 1
  push_cast
  ring

/-- `log (s_n²) / log n → (d+3)/(d+1)`. -/
private theorem tendsto_log_norming_sq {d : ℕ} {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) :
    Tendsto (fun n : ℕ => Real.log (norming d r n ^ 2) / Real.log n) atTop
      (𝓝 (((d : ℝ) + 3) / ((d : ℝ) + 1))) := by
  have hlogn : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => ((d : ℝ) + 3) * Real.log a / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogn
  have h2 := h1.add_const (((d : ℝ) + 3) / ((d : ℝ) + 1))
  rw [zero_add] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 1, hlogn.eventually_gt_atTop 0] with n hn hln
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  rw [norming_sq ha hr hn0, Real.log_pow, hr n, Real.log_mul ha.ne'
    (Real.rpow_pos_of_pos hnpos _).ne', Real.log_rpow hnpos]
  push_cast
  have : Real.log n ≠ 0 := hln.ne'
  have hd1 : ((d : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- The squared norm changes by at most `2 |x| + 1` under a unit step. -/
private theorem abs_sq_euclidNorm_add_le {d : ℕ} (x e : Site d) (he : e ∈ unitSteps d) :
    |euclidNorm (x + e) ^ 2 - euclidNorm x ^ 2| ≤ 2 * euclidNorm x + 1 := by
  rw [mem_unitSteps] at he
  obtain ⟨i, rfl | rfl⟩ := he
  · rw [euclidNorm_add_unit_sq]
    have h := abs_coord_le_euclidNorm x i
    rw [abs_le] at h ⊢
    constructor <;> linarith [h.1, h.2]
  · rw [← sub_eq_add_neg, euclidNorm_sub_unit_sq]
    have h := abs_coord_le_euclidNorm x i
    rw [abs_le] at h ⊢
    constructor <;> linarith [h.1, h.2]

/-- Almost surely every increment of the Dynkin martingale of `|x|²` is at most `4 |X_t| + 2`. -/
private theorem ae_abs_dynkin_sq_succ_sub_le {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    (hεd : ε < 1 / (d : ℝ)) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) :
    ∀ᵐ ω ∂μ, ∀ t : ℕ,
      |dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (t + 1) ω
        - dynkin ε (fun z : Site d => euclidNorm z ^ 2) X t ω| ≤ 4 * euclidNorm (X t ω) + 2 := by
  filter_upwards [ae_abs_dynkin_succ_sub_le hd hε hεd hX (fun z : Site d => euclidNorm z ^ 2)]
    with ω hω t
  have := hω t (2 * euclidNorm (X t ω) + 1) fun e he => abs_sq_euclidNorm_add_le _ e he
  linarith

/-- The Dynkin martingale of `|x|²` is in `L²` at each time. -/
private theorem memLp_dynkin_sq {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    (hεd : ε < 1 / (d : ℝ)) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) (n : ℕ) :
    MemLp (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n) 2 μ := by
  have hmart := martingale_dynkin hd hε hεd hX (fun z : Site d => euclidNorm z ^ 2)
  refine MemLp.of_bound
    ((hmart.stronglyMeasurable n).mono ((pathFiltration hX.measurable).le n)).aestronglyMeasurable
    (n * (4 * n + 2)) ?_
  filter_upwards [ae_abs_dynkin_sq_succ_sub_le hd hε hεd hX, ae_euclidNorm_le hd hε hεd hX]
    with ω h1 h2
  have hsum : dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω =
      ∑ t ∈ Finset.range n, (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (t + 1) ω
        - dynkin ε (fun z : Site d => euclidNorm z ^ 2) X t ω) := by
    rw [Finset.sum_range_sub (fun t => dynkin ε (fun z : Site d => euclidNorm z ^ 2) X t ω)]
    simp
  rw [Real.norm_eq_abs, hsum]
  calc |∑ t ∈ Finset.range n, (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (t + 1) ω
        - dynkin ε (fun z : Site d => euclidNorm z ^ 2) X t ω)|
      ≤ ∑ t ∈ Finset.range n, |dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (t + 1) ω
        - dynkin ε (fun z : Site d => euclidNorm z ^ 2) X t ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ Finset.range n, ((4 * n + 2 : ℕ) : ℝ) := by
        refine Finset.sum_le_sum fun t ht => ?_
        have htn : (t : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.1 ht).le
        have := h2 t
        push_cast
        linarith [h1 t]
    _ = n * (4 * n + 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- A function of the departure range at time `n` is measurable. -/
private theorem measurable_departureRange_fun {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Site d} (hX : ∀ n, Measurable (X n)) (n : ℕ) (G : Finset (Site d) → ℝ) :
    Measurable (fun ω => G (departureRange (fun j => X j ω) n)) := by
  have h : (fun ω => G (departureRange (fun j => X j ω) n)) =
      fun ω => (fun p : (i : Finset.Iic n) → Site d =>
        G ((Finset.range n).image (extendPath p))) (pastPath X n ω) := by
    funext ω
    congr 1
    unfold departureRange
    refine Finset.image_congr fun j hj => ?_
    exact (extendPath_pastPath X (Nat.le_of_lt (Finset.mem_range.1 hj)) ω).symm
  rw [h]
  exact (measurable_of_countable (fun p : (i : Finset.Iic n) → Site d =>
    G ((Finset.range n).image (extendPath p)))).comp (measurable_pastPath hX n)

/-- The limit `8 d ε ω_d / ((d+2)(d+3))` of the bracket of the Dynkin martingale of `|x|²` over
`r_n^{d+3}`. -/
private noncomputable def bracketLimit (d : ℕ) (ε : ℝ) : ℝ :=
  8 * d * ε * unitBallVolume d / ((d + 2) * (d + 3))

/-- The central limit theorem and the law of the iterated logarithm for the Dynkin martingale of
`|x|²`, normalized by `r_n^{(d+3)/2}`. -/
private theorem dynkin_sq_laws {d : ℕ} (hd : 2 ≤ d) (hCLT : MartingaleCLT.{u})
    (hLIL : StoutLIL.{u}) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ)) {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → Site d)
    (hX : IsCERW μ ε X) {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
    (hloc : ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ y : Site d,
      |(localTime (fun j => X j ω) n y : ℝ) - 2 * d * ε * max (r n - euclidNorm y) 0|
        ≤ η * r n)
    (hmax : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, maxRadius (fun j => X j ω) n ≤ 2 * r n) :
    TendstoInDistribution
      (fun n ω => dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n) atTop id
      (fun _ => μ) (gaussianReal 0 (bracketLimit d ε).toNNReal) ∧
    ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
      (∀ᶠ n : ℕ in atTop,
        σ * dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n
          ≤ (Real.sqrt (bracketLimit d ε) + δ) * Real.sqrt (2 * Real.log (Real.log n))) ∧
      (∃ᶠ n : ℕ in atTop,
        (Real.sqrt (bracketLimit d ε) - δ) * Real.sqrt (2 * Real.log (Real.log n))
          ≤ σ * dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n) := by
  have hd1 : 1 ≤ d := by omega
  have hε0 : 0 ≤ ε := hε.le
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hVpos : 0 < bracketLimit d ε := by
    unfold bracketLimit
    positivity
  set ℱ := pathFiltration hX.measurable with hℱ
  set Q : ℕ → Ω → ℝ := dynkin ε (fun z : Site d => euclidNorm z ^ 2) X with hQ
  have hmart : Martingale Q ℱ μ := martingale_dynkin hd1 hε0 hεd hX _
  have hL2 : ∀ n, MemLp (Q n) 2 μ := memLp_dynkin_sq hd1 hε0 hεd hX
  have hQ0 : ∀ ω, Q 0 ω = 0 := fun ω => dynkin_zero ε _ X ω
  set B : ℕ → Ω → ℝ := fun n ω => 4 * euclidNorm (X (n - 1) ω) + 2 with hB
  have hB0 : ∀ n ω, 0 ≤ B n ω := fun n ω => by
    have := euclidNorm_nonneg (X (n - 1) ω)
    simp only [hB]
    linarith
  have hBm : ∀ n, StronglyMeasurable[ℱ n] (B (n + 1)) := fun n =>
    stronglyMeasurable_comp_pastPath hX.measurable n
      (fun p : (i : Finset.Iic n) → Site d =>
        4 * euclidNorm (p ⟨n, Finset.mem_Iic.2 le_rfl⟩) + 2)
  have hBb : ∀ᵐ ω ∂μ, ∀ n, |Q (n + 1) ω - Q n ω| ≤ B (n + 1) ω :=
    ae_abs_dynkin_sq_succ_sub_le hd1 hε0 hεd hX
  have hBbd : ∀ n, ∃ C, ∀ᵐ ω ∂μ, |B n ω| ≤ C := by
    intro n
    refine ⟨4 * n + 2, ?_⟩
    filter_upwards [ae_euclidNorm_le hd1 hε0 hεd hX] with ω hω'
    have h1 : euclidNorm (X (n - 1) ω) ≤ n := (hω' (n - 1)).trans (by exact_mod_cast Nat.sub_le n 1)
    have h2 := euclidNorm_nonneg (X (n - 1) ω)
    rw [abs_of_nonneg (hB0 n ω)]
    simp only [hB]
    linarith
  have hs := norming_pos ha hr
  have hs' := tendsto_norming_atTop ha hr
  have hrtend := tendsto_scale_atTop ha hr
  have hbr : ∀ᵐ ω ∂μ, Tendsto (fun n => predBracket μ ℱ Q Q n ω / norming d r n ^ 2) atTop
      (𝓝 (bracketLimit d ε)) := by
    filter_upwards [ae_predBracket_dynkin_sq hd1 hε0 hεd hX, hloc, hmax] with ω hbrω hlocω hmaxω
    have := tendsto_bracket_quotient hd1 hε hrtend (fun j => X j ω) hlocω hmaxω
    refine this.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [hbrω n, norming_sq ha hr hn]
  have hBmax : ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ i < n,
      B (i + 1) ω ≤ δ * norming d r n := by
    filter_upwards [hmax] with ω hmaxω δ hδ
    filter_upwards [hmaxω, (tendsto_scale_div hd ha hr).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < δ / 10)), hrtend.eventually_ge_atTop 1]
      with n h1 h2 h3 i hi
    have hsn := hs n
    have hX1 : euclidNorm (X i ω) ≤ maxRadius (fun j => X j ω) n :=
      euclidNorm_le_maxRadius (fun j => X j ω) hi.le
    have h4 : r n < δ / 10 * norming d r n := (div_lt_iff₀ hsn).1 h2
    show 4 * euclidNorm (X (i + 1 - 1) ω) + 2 ≤ δ * norming d r n
    rw [Nat.add_sub_cancel]
    linarith
  have hBs : ∀ᵐ ω ∂μ, Tendsto (fun n => B n ω ^ 2 / norming d r n) atTop (𝓝 0) := by
    filter_upwards [hmax] with ω hmaxω
    have hlim : Tendsto (fun n => 100 * (r n ^ 2 / norming d r n)) atTop (𝓝 0) := by
      simpa using (tendsto_scale_sq_div hd ha hr).const_mul 100
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => ?_) ?_ hlim
    · exact div_nonneg (sq_nonneg _) (hs n).le
    · filter_upwards [hmaxω, hrtend.eventually_ge_atTop 1] with n h1 h2
      have hX1 : euclidNorm (X (n - 1) ω) ≤ maxRadius (fun j => X j ω) n :=
        euclidNorm_le_maxRadius (fun j => X j ω) (Nat.sub_le n 1)
      have hBn : B n ω ≤ 10 * r n := by
        simp only [hB]
        linarith
      have hsn := hs n
      calc B n ω ^ 2 / norming d r n ≤ (10 * r n) ^ 2 / norming d r n :=
            div_le_div_of_nonneg_right (pow_le_pow_left₀ (hB0 n ω) hBn 2) hsn.le
        _ = 100 * (r n ^ 2 / norming d r n) := by ring
  refine ⟨clt_normalized hCLT μ ℱ Q hmart hL2 hQ0 B hBm hBb hBbd hs hVpos.le hBmax hbr, ?_⟩
  have hκ : 0 < ((d : ℝ) + 3) / ((d : ℝ) + 1) := by positivity
  have hlog := tendsto_log_norming_sq ha hr
  have key : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ →
      (∀ᶠ n : ℕ in atTop, σ * Q n ω / norming d r n
        ≤ (Real.sqrt (bracketLimit d ε) + δ) * Real.sqrt (2 * Real.log (Real.log n))) ∧
      (∃ᶠ n : ℕ in atTop, (Real.sqrt (bracketLimit d ε) - δ) *
        Real.sqrt (2 * Real.log (Real.log n)) ≤ σ * Q n ω / norming d r n) := by
    intro σ hσ
    have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
    set M : ℕ → Ω → ℝ := fun n ω => σ * Q n ω with hM
    have hMmart : Martingale M ℱ μ := hmart.smul σ
    have hML2 : ∀ n, MemLp (M n) 2 μ := fun n => (hL2 n).const_mul σ
    have hM0 : ∀ ω, M 0 ω = 0 := fun ω => by simp [hM, hQ0]
    have hMBb : ∀ᵐ ω ∂μ, ∀ n, |M (n + 1) ω - M n ω| ≤ B (n + 1) ω := by
      filter_upwards [hBb] with ω h n
      have : M (n + 1) ω - M n ω = σ * (Q (n + 1) ω - Q n ω) := by simp only [hM]; ring
      rw [this, abs_mul, hσabs, one_mul]
      exact h n
    have hbrM : ∀ n, predBracket μ ℱ M M n = predBracket μ ℱ Q Q n := by
      intro n
      unfold predBracket
      refine Finset.sum_congr rfl fun t _ => ?_
      congr 1
      funext ω
      have h1 : (M (t + 1) ω - M t ω) * (M (t + 1) ω - M t ω)
          = (σ * σ) * ((Q (t + 1) ω - Q t ω) * (Q (t + 1) ω - Q t ω)) := by
        simp only [hM]
        ring
      rw [h1, hσ2, one_mul]
    have hMbr : ∀ᵐ ω ∂μ, Tendsto (fun n => predBracket μ ℱ M M n ω / norming d r n ^ 2)
        atTop (𝓝 (bracketLimit d ε)) := by
      filter_upwards [hbr] with ω h
      simpa only [hbrM] using h
    exact lil_normalized hLIL μ ℱ M hMmart hML2 hM0 B hB0 hBm hMBb hs hs' hVpos hκ hMbr hBs hlog
  filter_upwards [key 1 (Or.inl rfl), key (-1) (Or.inr rfl)] with ω h1 h2 δ hδ σ hσ
  rcases hσ with rfl | rfl
  · exact h1 δ hδ
  · exact h2 δ hδ

/-- Convergence in distribution to a variable with the same law. -/
private theorem tendstoInDistribution_of_map_eq {Ω Ω' Ω'' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace Ω''] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {ν : Measure Ω''} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {W : Ω'' → ℝ}
    (h : TendstoInDistribution X atTop Z (fun _ => μ) μ') (hW : AEMeasurable W ν)
    (hmap : μ'.map Z = ν.map W) : TendstoInDistribution X atTop W (fun _ => μ) ν := by
  refine ⟨h.forall_aemeasurable, hW, ?_⟩
  have e : (⟨ν.map W, Measure.isProbabilityMeasure_map hW⟩ : ProbabilityMeasure ℝ) =
      ⟨μ'.map Z, Measure.isProbabilityMeasure_map h.aemeasurable_limit⟩ :=
    Subtype.ext hmap.symm
  rw [e]
  exact h.tendsto

/-- For a path from the origin, the sum of the distances over the departure range, centered at
`n/(2ε)`, is `(𝒬_n - |X_n|²)/(2ε)`, where `𝒬` is the Dynkin martingale of `|x|²`. -/
private theorem sum_sub_eq_dynkin {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {Ω : Type*}
    (X : ℕ → Ω → Site d) (ω : Ω) (h0 : X 0 ω = 0) (n : ℕ) (D : ℝ) :
    (∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x - n / (2 * ε)) / D =
      (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / D
        - euclidNorm (X n ω) ^ 2 / D) / (2 * ε) := by
  have h := sq_euclidNorm_eq hd ε X ω h0 n
  have h2 : ∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x - n / (2 * ε) =
      (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω - euclidNorm (X n ω) ^ 2)
        / (2 * ε) := by
    field_simp
    linarith
  rw [h2, div_right_comm, sub_div]

/-- Factoring `R_mom^{d+1} - r^{d+1}`: for `n ≥ 1`,
`(R_mom - r) / r^{(3-d)/2} = ((d+1)/(d ω_d Σ_{j ≤ d} (R_mom/r)^j)) · ((Σ - n/(2ε)) / r^{(d+3)/2})`,
where `Σ` is the sum of the distances and `R_mom` the moment radius. -/
private theorem moment_radius_identity {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {Sg : ℝ}
    (hSg : 0 ≤ Sg) {n : ℕ} (hn : n ≠ 0) {r : ℝ} (hr : 0 < r)
    (hrpow : r ^ (d + 1) = (d + 1) * n / (2 * d * ε * unitBallVolume d)) :
    (((d + 1) / (d * unitBallVolume d) * Sg) ^ ((1 : ℝ) / (d + 1)) - r) /
        r ^ ((3 - (d : ℝ)) / 2) =
      ((d + 1) / (d * unitBallVolume d * ∑ j ∈ Finset.range (d + 1),
          (((d + 1) / (d * unitBallVolume d) * Sg) ^ ((1 : ℝ) / (d + 1)) / r) ^ j)) *
        ((Sg - n / (2 * ε)) / r ^ (((d : ℝ) + 3) / 2)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  set ω := unitBallVolume d with hωdef
  set Rm : ℝ := ((d + 1) / (d * ω) * Sg) ^ ((1 : ℝ) / (d + 1)) with hRm
  have hRm0 : 0 ≤ Rm := Real.rpow_nonneg (by positivity) _
  have hRmpow : Rm ^ (d + 1) = (d + 1) / (d * ω) * Sg := by
    rw [hRm, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have : ((1 : ℝ) / (d + 1)) * ((d + 1 : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [this, Real.rpow_one]
  set ρ : ℝ := Rm / r with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg hRm0 hr.le
  have hRmρ : Rm = ρ * r := by rw [hρ]; field_simp
  set G : ℝ := ∑ j ∈ Finset.range (d + 1), ρ ^ j with hG
  have hG1 : 1 ≤ G := by
    have h := Finset.single_le_sum (f := fun j : ℕ => ρ ^ j) (fun j _ => pow_nonneg hρ0 j)
      (Finset.mem_range.2 (Nat.succ_pos d))
    simpa using h
  have hGpos : 0 < G := by linarith
  have hgeom : G * (ρ - 1) = ρ ^ (d + 1) - 1 := geom_sum_mul ρ (d + 1)
  have hkey : (d + 1) / (d * ω) * (Sg - n / (2 * ε)) = r ^ (d + 1) * G * (ρ - 1) := by
    have h1 : (d + 1) / (d * ω) * (Sg - n / (2 * ε)) = Rm ^ (d + 1) - r ^ (d + 1) := by
      rw [hRmpow, hrpow]
      field_simp
    rw [h1, hRmρ, mul_pow, mul_assoc, hgeom]
    ring
  have hexp : r ^ (((d : ℝ) + 3) / 2) = r ^ d * r ^ ((3 - (d : ℝ)) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr]
    congr 1
    ring
  have htpos : 0 < r ^ ((3 - (d : ℝ)) / 2) := Real.rpow_pos_of_pos hr _
  set t := r ^ ((3 - (d : ℝ)) / 2) with ht
  rw [hexp]
  have hrd : 0 < r ^ d := pow_pos hr d
  have e1 : (d + 1) / (d * ω * G) * ((Sg - n / (2 * ε)) / (r ^ d * t))
      = ((d + 1) / (d * ω) * (Sg - n / (2 * ε))) / (G * (r ^ d * t)) := by
    field_simp
  rw [e1, hkey, hRmρ]
  field_simp
  ring

/-- The moment radius over `r_n` tends to `1` when `2ε Σ_n / n → 1`. -/
private theorem tendsto_moment_ratio {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {r : ℕ → ℝ}
    (hr : ∀ n, r n = ((d + 1) * n / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1)))
    {Sg : ℕ → ℝ} (hSg : ∀ n, 0 ≤ Sg n)
    (hlim : Tendsto (fun n : ℕ => 2 * ε * Sg n / n) atTop (𝓝 1)) :
    Tendsto (fun n => ((d + 1) / (d * unitBallVolume d) * Sg n) ^ ((1 : ℝ) / (d + 1)) / r n)
      atTop (𝓝 1) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hcont : Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / (d + 1))) (𝓝 1) (𝓝 1) := by
    have := (Real.continuousAt_rpow_const (1 : ℝ) ((1 : ℝ) / (d + 1)) (Or.inl one_ne_zero)).tendsto
    simpa using this
  refine (hcont.comp hlim).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  simp only [Function.comp]
  rw [hr n, ← Real.div_rpow (by have := hSg n; positivity) (by positivity)]
  congr 1
  field_simp

/-- `r_n² / n → 0` for `d ≥ 2`, when `r_n^{d+1} = (d+1) n / (2 d ε ω_d)`. -/
private theorem tendsto_scale_sq_div_nat {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {r : ℕ → ℝ}
    (hrtend : Tendsto r atTop atTop)
    (hrpow : ∀ n, r n ^ (d + 1) = (d + 1) * n / (2 * d * ε * unitBallVolume d)) :
    Tendsto (fun n : ℕ => r n ^ 2 / n) atTop (𝓝 0) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hlim : Tendsto (fun n : ℕ => (d + 1) / (2 * d * ε * unitBallVolume d) * (r n)⁻¹) atTop
      (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hrtend).const_mul
      (((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d))
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => ?_) ?_ hlim
  · have := Nat.cast_nonneg (α := ℝ) n
    positivity
  · filter_upwards [hrtend.eventually_ge_atTop 1, eventually_ne_atTop 0] with n h1 hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    have hrpos : 0 < r n := by linarith
    have hn' : (n : ℝ) = 2 * d * ε * unitBallVolume d * r n ^ (d + 1) / (d + 1) := by
      have := hrpow n
      field_simp at this ⊢
      linarith
    have h3 : r n ^ 3 ≤ r n ^ (d + 1) := pow_le_pow_right₀ h1 (by omega)
    rw [div_le_iff₀ hnpos, hn']
    have hc : 0 < (d + 1 : ℝ) / (2 * d * ε * unitBallVolume d) := by positivity
    calc r n ^ 2 = (d + 1) / (2 * d * ε * unitBallVolume d) * (r n)⁻¹ *
          (2 * d * ε * unitBallVolume d * r n ^ 3 / (d + 1)) := by
          field_simp
      _ ≤ (d + 1) / (2 * d * ε * unitBallVolume d) * (r n)⁻¹ *
          (2 * d * ε * unitBallVolume d * r n ^ (d + 1) / (d + 1)) := by
          gcongr

/-- `log log n / r_n → 0`. -/
private theorem tendsto_loglog_div_scale {d : ℕ} {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) :
    Tendsto (fun n : ℕ => Real.log (Real.log n) / r n) atTop (𝓝 0) := by
  have h1 := CERW.Support.Main.tendsto_log_rpow_div_rpow 1 (c := 1 / ((d : ℝ) + 1))
    (by positivity)
  have h2 : Tendsto (fun n : ℕ => a⁻¹ * (Real.log ((n : ℝ) + 2) ^ (1 : ℝ) /
      (n : ℝ) ^ (1 / ((d : ℝ) + 1)))) atTop (𝓝 0) := by
    simpa using h1.const_mul a⁻¹
  refine squeeze_zero' ?_ ?_ h2
  · filter_upwards [eventually_ge_atTop 3] with n hn
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog1 : 1 ≤ Real.log n := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_three
      linarith
    have hrpos : 0 ≤ r n := by
      rw [hr n]
      positivity
    exact div_nonneg (Real.log_nonneg hlog1) hrpos
  · filter_upwards [eventually_ge_atTop 3] with n hn
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
    have hll : Real.log (Real.log n) ≤ Real.log ((n : ℝ) + 2) := by
      have h3 := Real.log_le_sub_one_of_pos hlogpos
      have h4 : Real.log n ≤ Real.log ((n : ℝ) + 2) := Real.log_le_log hnpos (by linarith)
      linarith
    have hc : 0 < (n : ℝ) ^ (1 / ((d : ℝ) + 1)) := Real.rpow_pos_of_pos hnpos _
    rw [hr n, Real.rpow_one]
    calc Real.log (Real.log n) / (a * (n : ℝ) ^ (1 / ((d : ℝ) + 1)))
        ≤ Real.log ((n : ℝ) + 2) / (a * (n : ℝ) ^ (1 / ((d : ℝ) + 1))) :=
          div_le_div_of_nonneg_right hll (by positivity)
      _ = a⁻¹ * (Real.log ((n : ℝ) + 2) / (n : ℝ) ^ (1 / ((d : ℝ) + 1))) := by
          field_simp

/-- `s_n √(2 log log n) / n → 0` for `d ≥ 2`. -/
private theorem tendsto_norming_loglog_div {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {a : ℝ}
    (ha : 0 < a) {r : ℕ → ℝ} (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
    (hrpow : ∀ n, r n ^ (d + 1) = (d + 1) * n / (2 * d * ε * unitBallVolume d)) :
    Tendsto (fun n : ℕ => norming d r n * Real.sqrt (2 * Real.log (Real.log n)) / n) atTop
      (𝓝 0) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hrtend := tendsto_scale_atTop ha hr
  set C₁ : ℝ := 2 * d * ε * unitBallVolume d / (d + 1) with hC₁
  have hC₁pos : 0 < C₁ := by positivity
  have hg := tendsto_loglog_div_scale ha hr
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (2 / C₁ ^ 2 * (Real.log (Real.log n) / r n)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 2 / C₁ ^ 2 * (Real.log (Real.log n) / r n)) atTop (𝓝 0) := by
      simpa using hg.const_mul (2 / C₁ ^ 2)
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at h2
    exact h2
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop 3] with n hn
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_nonneg (mul_nonneg (norming_pos ha hr n).le (Real.sqrt_nonneg _))
      (by linarith)
  · filter_upwards [eventually_ge_atTop 3, hrtend.eventually_ge_atTop 1] with n hn h1
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : n ≠ 0 := by omega
    have hnpos : (0 : ℝ) < n := by linarith
    have hrpos : 0 < r n := by linarith
    have hlogn : 1 ≤ Real.log n := by
      rw [Real.le_log_iff_exp_le hnpos]
      have := Real.exp_one_lt_three
      linarith
    have hll : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hlogn
    have hnC : (n : ℝ) = C₁ * r n ^ (d + 1) := by
      have := hrpow n
      rw [hC₁]
      field_simp at this ⊢
      linarith
    have hsq : (norming d r n * Real.sqrt (2 * Real.log (Real.log n)) / n) ^ 2
        = 2 / C₁ ^ 2 * Real.log (Real.log n) * (r n ^ (d + 3) / r n ^ (2 * d + 2)) := by
      rw [div_pow, mul_pow, norming_sq ha hr hn0, Real.sq_sqrt (by linarith)]
      have : (n : ℝ) ^ 2 = C₁ ^ 2 * r n ^ (2 * d + 2) := by
        rw [hnC, mul_pow, ← pow_mul]
        ring_nf
      rw [this]
      field_simp
    have hfrac : r n ^ (d + 3) / r n ^ (2 * d + 2) ≤ 1 / r n := by
      rw [div_le_div_iff₀ (pow_pos hrpos _) hrpos]
      have : r n ^ (d + 3) * r n = r n ^ (d + 4) := by ring
      rw [this, one_mul]
      exact pow_le_pow_right₀ h1 (by omega)
    have hbound : (norming d r n * Real.sqrt (2 * Real.log (Real.log n)) / n) ^ 2
        ≤ 2 / C₁ ^ 2 * (Real.log (Real.log n) / r n) := by
      rw [hsq]
      calc 2 / C₁ ^ 2 * Real.log (Real.log n) * (r n ^ (d + 3) / r n ^ (2 * d + 2))
          ≤ 2 / C₁ ^ 2 * Real.log (Real.log n) * (1 / r n) :=
            mul_le_mul_of_nonneg_left hfrac (by positivity)
        _ = 2 / C₁ ^ 2 * (Real.log (Real.log n) / r n) := by ring
    exact (le_abs_self _).trans (Real.abs_le_sqrt hbound)

/-- The sum of the distances over the departure range is asymptotically `n / (2ε)`: if
`2ε Σ_n = n + q_n - x_n` with `q_n = O(s_n √(2 log log n))` and `0 ≤ x_n ≤ 4 r_n²`, then
`2ε Σ_n / n → 1`. -/
private theorem tendsto_sum_ratio {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {a : ℝ}
    (ha : 0 < a) {r : ℕ → ℝ} (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
    (hrpow : ∀ n, r n ^ (d + 1) = (d + 1) * n / (2 * d * ε * unitBallVolume d))
    {Sg q x2 : ℕ → ℝ} (hid : ∀ n, 2 * ε * Sg n = n + q n - x2 n) {C : ℝ}
    (hq : ∀ᶠ n : ℕ in atTop,
      |q n| ≤ C * (norming d r n * Real.sqrt (2 * Real.log (Real.log n))))
    (hx : ∀ᶠ n : ℕ in atTop, 0 ≤ x2 n ∧ x2 n ≤ 4 * r n ^ 2) :
    Tendsto (fun n : ℕ => 2 * ε * Sg n / n) atTop (𝓝 1) := by
  have hrtend := tendsto_scale_atTop ha hr
  have h1 : Tendsto (fun n : ℕ => |C| * (norming d r n * Real.sqrt (2 * Real.log (Real.log n))
      / n)) atTop (𝓝 0) := by
    simpa using (tendsto_norming_loglog_div hd hε ha hr hrpow).const_mul |C|
  have h2 : Tendsto (fun n : ℕ => 4 * (r n ^ 2 / n)) atTop (𝓝 0) := by
    simpa using (tendsto_scale_sq_div_nat hd hε hrtend hrpow).const_mul 4
  have hqn : Tendsto (fun n : ℕ => q n / n) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h1
    filter_upwards [hq, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hnpos, ← mul_div_assoc]
    refine div_le_div_of_nonneg_right (hn.trans ?_) hnpos.le
    exact mul_le_mul_of_nonneg_right (le_abs_self C)
      (mul_nonneg (norming_pos ha hr n).le (Real.sqrt_nonneg _))
  have hxn : Tendsto (fun n : ℕ => x2 n / n) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ h2
    · filter_upwards [hx] with n hn
      exact div_nonneg hn.1 (Nat.cast_nonneg n)
    · filter_upwards [hx, eventually_ge_atTop 1] with n hn hn1
      have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn1
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hn.2 hnpos.le
  have h3 := ((tendsto_const_nhds (x := (1 : ℝ))).add hqn).sub hxn
  rw [add_zero, sub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn1
  rw [hid n]
  field_simp

/-- Dividing a centered Gaussian by a constant `c` divides its variance by `c²`. -/
private theorem gaussianReal_map_div_toNNReal {V c : ℝ} (hV : 0 ≤ V) :
    (gaussianReal 0 V.toNNReal).map (· / c) = gaussianReal 0 (V / c ^ 2).toNNReal := by
  rw [gaussianReal_map_div_const, zero_div]
  congr 1
  apply NNReal.eq
  have : 0 ≤ V / c ^ 2 := div_nonneg hV (sq_nonneg c)
  rw [NNReal.coe_div, Real.coe_toNNReal _ this, Real.coe_toNNReal _ hV]
  rfl

/-- Multiplying a centered Gaussian by a constant `c` multiplies its variance by `c²`. -/
private theorem gaussianReal_map_mul_toNNReal {V : ℝ} (c : ℝ) (hV : 0 ≤ V) :
    (gaussianReal 0 V.toNNReal).map (c * ·) = gaussianReal 0 (c ^ 2 * V).toNNReal := by
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  apply NNReal.eq
  have : 0 ≤ c ^ 2 * V := mul_nonneg (sq_nonneg c) hV
  rw [NNReal.coe_mul, Real.coe_toNNReal _ this, Real.coe_toNNReal _ hV]
  rfl

/-- The variance `2 d ω_d / (ε (d+2)(d+3))` in the central limit theorem for the sum. -/
private noncomputable def sumVariance (d : ℕ) (ε : ℝ) : ℝ :=
  2 * d * unitBallVolume d / (ε * (d + 2) * (d + 3))

/-- The variance `2 / (ε d ω_d (d+2)(d+3))` in the central limit theorem for the radius. -/
private noncomputable def radiusVariance (d : ℕ) (ε : ℝ) : ℝ :=
  2 / (ε * d * unitBallVolume d * (d + 2) * (d + 3))

/-- The variance of the sum is the bracket limit divided by `(2ε)²`. -/
private theorem sumVariance_eq (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    sumVariance d ε = bracketLimit d ε / (2 * ε) ^ 2 := by
  unfold sumVariance bracketLimit
  have : (d : ℝ) + 2 ≠ 0 := by positivity
  have : (d : ℝ) + 3 ≠ 0 := by positivity
  field_simp
  ring

/-- The variance of the radius is the variance of the sum divided by `(d ω_d)²`. -/
private theorem radiusVariance_eq {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    radiusVariance d ε = sumVariance d ε / (d * unitBallVolume d) ^ 2 := by
  unfold radiusVariance sumVariance
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hω := unitBallVolume_pos d
  have : (d : ℝ) + 2 ≠ 0 := by positivity
  have : (d : ℝ) + 3 ≠ 0 := by positivity
  field_simp

/-- The bracket limit is positive. -/
private theorem bracketLimit_pos {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    0 < bracketLimit d ε := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hω := unitBallVolume_pos d
  unfold bracketLimit
  positivity

/-- The central limit theorem for the sum of the distances from the origin. -/
private theorem sum_clt {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : IsCERW μ ε X) {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
    (hmax : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, maxRadius (fun j => X j ω) n ≤ 2 * r n)
    (hQ1 : TendstoInDistribution
      (fun n ω => dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n) atTop id
      (fun _ => μ) (gaussianReal 0 (bracketLimit d ε).toNNReal)) :
    TendstoInDistribution
      (fun n ω => (∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x - n / (2 * ε)) /
        r n ^ (((d : ℝ) + 3) / 2)) atTop id (fun _ => μ)
      (gaussianReal 0 (sumVariance d ε).toNNReal) := by
  have hd1 : 1 ≤ d := by omega
  have hVpos := bracketLimit_pos hd1 hε
  have hT := hQ1.continuous_comp (g := fun x : ℝ => x / (2 * ε)) (by fun_prop)
  have hT' : TendstoInDistribution
      (fun n ω => (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n)
        / (2 * ε)) atTop id (fun _ => μ) (gaussianReal 0 (sumVariance d ε).toNNReal) := by
    refine tendstoInDistribution_of_map_eq hT measurable_id.aemeasurable ?_
    rw [sumVariance_eq d hε]
    simp only [Function.comp_def, id, Measure.map_id]
    exact gaussianReal_map_div_toNNReal hVpos.le
  have hX0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
    rw [ae_iff]
    exact hX.start
  have hSmeas : ∀ n, Measurable (fun ω => (∑ x ∈ departureRange (fun j => X j ω) n,
      euclidNorm x - n / (2 * ε)) / r n ^ (((d : ℝ) + 3) / 2)) := fun n =>
    measurable_departureRange_fun hX.measurable n
      (fun A => (∑ x ∈ A, euclidNorm x - n / (2 * ε)) / r n ^ (((d : ℝ) + 3) / 2))
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hT' ?_
    (fun n => (hSmeas n).aemeasurable)
  refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
  · exact (((hSmeas n).aemeasurable).sub ((hT'.forall_aemeasurable n))).aestronglyMeasurable
  · filter_upwards [hX0, hmax] with ω h0 hm
    have hlim : Tendsto (fun n => 2 / ε * (r n ^ 2 / norming d r n)) atTop (𝓝 0) := by
      simpa using (tendsto_scale_sq_div hd ha hr).const_mul (2 / ε)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hm, eventually_ne_atTop 0] with n hn hn0
    have hs := norming_pos ha hr n
    have hDeq : r n ^ (((d : ℝ) + 3) / 2) = norming d r n := by
      simp only [norming, if_neg hn0]
    have hXn : euclidNorm (X n ω) ≤ 2 * r n :=
      (euclidNorm_le_maxRadius (fun j => X j ω) le_rfl).trans hn
    have hXn0 := euclidNorm_nonneg (X n ω)
    simp only [Pi.sub_apply]
    rw [sum_sub_eq_dynkin hd1 hε X ω h0 n, hDeq, Real.norm_eq_abs]
    have h1 : (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n
          - euclidNorm (X n ω) ^ 2 / norming d r n) / (2 * ε)
        - dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n / (2 * ε)
        = -(euclidNorm (X n ω) ^ 2 / norming d r n / (2 * ε)) := by ring
    rw [h1, abs_neg, abs_of_nonneg (by positivity)]
    have h2 : euclidNorm (X n ω) ^ 2 ≤ (2 * r n) ^ 2 := pow_le_pow_left₀ hXn0 hXn 2
    calc euclidNorm (X n ω) ^ 2 / norming d r n / (2 * ε)
        ≤ (2 * r n) ^ 2 / norming d r n / (2 * ε) := by gcongr
      _ = 2 / ε * (r n ^ 2 / norming d r n) := by
          field_simp

/-- The square root of the variance of the sum is `√(bracket limit) / (2ε)`. -/
private theorem sqrt_sumVariance {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    Real.sqrt (sumVariance d ε) = (2 * ε)⁻¹ * Real.sqrt (bracketLimit d ε) := by
  rw [sumVariance_eq d hε, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (by positivity)]
  ring

/-- The law of the iterated logarithm for the sum of the distances from the origin. -/
private theorem sum_lil {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → Site d)
    (hX : IsCERW μ ε X) {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
    (hmax : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, maxRadius (fun j => X j ω) n ≤ 2 * r n)
    (hQ2 : ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
      (∀ᶠ n : ℕ in atTop,
        σ * dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n
          ≤ (Real.sqrt (bracketLimit d ε) + δ) * Real.sqrt (2 * Real.log (Real.log n))) ∧
      (∃ᶠ n : ℕ in atTop,
        (Real.sqrt (bracketLimit d ε) - δ) * Real.sqrt (2 * Real.log (Real.log n))
          ≤ σ * dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n)) :
    ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
      (∀ᶠ n : ℕ in atTop,
        σ * ((∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x - n / (2 * ε)) /
          r n ^ (((d : ℝ) + 3) / 2))
          ≤ (Real.sqrt (sumVariance d ε) + δ) * Real.sqrt (2 * Real.log (Real.log n))) ∧
      (∃ᶠ n : ℕ in atTop,
        (Real.sqrt (sumVariance d ε) - δ) * Real.sqrt (2 * Real.log (Real.log n))
          ≤ σ * ((∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x - n / (2 * ε)) /
            r n ^ (((d : ℝ) + 3) / 2))) := by
  have hd1 : 1 ≤ d := by omega
  have hX0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
    rw [ae_iff]
    exact hX.start
  have hVpos := bracketLimit_pos hd1 hε
  have hloglogn : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hLtop : Tendsto (fun n : ℕ => Real.sqrt (2 * Real.log (Real.log n))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (hloglogn.const_mul_atTop two_pos)
  have hL : ∀ᶠ n : ℕ in atTop, 0 < Real.sqrt (2 * Real.log (Real.log n)) :=
    hLtop.eventually_gt_atTop 0
  filter_upwards [hQ2, hX0, hmax] with ω hQ h0 hm δ hδ σ hσ
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hmul := lil_mul_seq (a := fun n => σ * dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω
      / norming d r n) (A := fun _ => (2 * ε)⁻¹) (c := Real.sqrt (bracketLimit d ε))
    (κ := (2 * ε)⁻¹) (Real.sqrt_pos.2 hVpos) (by positivity) hL tendsto_const_nhds
    (fun δ' hδ' => hQ δ' hδ' σ hσ)
  set e : ℕ → ℝ := fun n => -(σ * euclidNorm (X n ω) ^ 2 / norming d r n) / (2 * ε) with he
  have he0 : Tendsto e atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => 2 / ε * (r n ^ 2 / norming d r n)) atTop (𝓝 0) := by
      simpa using (tendsto_scale_sq_div hd ha hr).const_mul (2 / ε)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hm] with n hn
    have hs := norming_pos ha hr n
    have hXn : euclidNorm (X n ω) ≤ 2 * r n :=
      (euclidNorm_le_maxRadius (fun j => X j ω) le_rfl).trans hn
    have hXn0 := euclidNorm_nonneg (X n ω)
    have h2 : euclidNorm (X n ω) ^ 2 ≤ (2 * r n) ^ 2 := pow_le_pow_left₀ hXn0 hXn 2
    simp only [he]
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_div, abs_mul, hσabs, one_mul,
      abs_of_nonneg (sq_nonneg _), abs_of_pos hs, abs_of_pos (by positivity : 0 < 2 * ε)]
    calc euclidNorm (X n ω) ^ 2 / norming d r n / (2 * ε)
        ≤ (2 * r n) ^ 2 / norming d r n / (2 * ε) := by gcongr
      _ = 2 / ε * (r n ^ 2 / norming d r n) := by
          field_simp
  have hadd := lil_add_small hL (he0.div_atTop hLtop) hmul δ hδ
  have hsq : Real.sqrt (sumVariance d ε) = (2 * ε)⁻¹ * Real.sqrt (bracketLimit d ε) :=
    sqrt_sumVariance hε
  have hidn : ∀ n : ℕ, n ≠ 0 →
      σ * ((∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x - n / (2 * ε)) /
          r n ^ (((d : ℝ) + 3) / 2))
        = (2 * ε)⁻¹ * (σ * dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω
          / norming d r n) + e n := by
    intro n hn
    have hDeq : r n ^ (((d : ℝ) + 3) / 2) = norming d r n := by
      simp only [norming, if_neg hn]
    rw [sum_sub_eq_dynkin hd1 hε X ω h0 n, hDeq]
    simp only [he]
    ring
  rw [hsq]
  refine ⟨?_, ?_⟩
  · filter_upwards [hadd.1, eventually_ne_atTop 0] with n hn hn0
    rw [hidn n hn0]
    exact hn
  · refine (hadd.2.and_eventually (eventually_ne_atTop 0)).mono fun n ⟨hn, hn0⟩ => ?_
    rw [hidn n hn0]
    exact hn

/-- Almost surely, `2ε Σ_{x ∈ A_n} |x| / n → 1`. -/
private theorem ae_sum_ratio {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → Site d)
    (hX : IsCERW μ ε X) {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
    (hrpow : ∀ n, r n ^ (d + 1) = (d + 1) * n / (2 * d * ε * unitBallVolume d))
    (hmax : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, maxRadius (fun j => X j ω) n ≤ 2 * r n)
    (hQ2 : ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
      (∀ᶠ n : ℕ in atTop,
        σ * dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n
          ≤ (Real.sqrt (bracketLimit d ε) + δ) * Real.sqrt (2 * Real.log (Real.log n))) ∧
      (∃ᶠ n : ℕ in atTop,
        (Real.sqrt (bracketLimit d ε) - δ) * Real.sqrt (2 * Real.log (Real.log n))
          ≤ σ * dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      2 * ε * (∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x) / n) atTop (𝓝 1) := by
  have hd1 : 1 ≤ d := by omega
  have hX0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
    rw [ae_iff]
    exact hX.start
  filter_upwards [hQ2, hX0, hmax] with ω hQ h0 hm
  refine tendsto_sum_ratio hd hε ha hr hrpow
    (Sg := fun n => ∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x)
    (q := fun n => dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω)
    (x2 := fun n => euclidNorm (X n ω) ^ 2) ?_ (C := Real.sqrt (bracketLimit d ε) + 1) ?_ ?_
  · intro n
    have h := sq_euclidNorm_eq hd1 ε X ω h0 n
    linarith
  · filter_upwards [(hQ 1 one_pos 1 (Or.inl rfl)).1, (hQ 1 one_pos (-1) (Or.inr rfl)).1]
      with n h1 h2
    have hs := norming_pos ha hr n
    rw [abs_le]
    rw [one_mul] at h1
    rw [neg_one_mul] at h2
    have h1' := (div_le_iff₀ hs).1 h1
    have h2' := (div_le_iff₀ hs).1 h2
    constructor <;> linarith
  · filter_upwards [hm] with n hn
    have hXn : euclidNorm (X n ω) ≤ 2 * r n :=
      (euclidNorm_le_maxRadius (fun j => X j ω) le_rfl).trans hn
    have hXn0 := euclidNorm_nonneg (X n ω)
    refine ⟨sq_nonneg _, ?_⟩
    calc euclidNorm (X n ω) ^ 2 ≤ (2 * r n) ^ 2 := pow_le_pow_left₀ hXn0 hXn 2
      _ = 4 * r n ^ 2 := by ring

/-- The factor `(d+1)/(d ω_d Σ_{j ≤ d} (R_mom/r)^j)` by which the centered sum is multiplied to get
the centered moment radius, for a sum `Σ` of distances and a scale `r`. -/
private noncomputable def radiusFactor (d : ℕ) (Sg r : ℝ) : ℝ :=
  (d + 1) / (d * unitBallVolume d * ∑ j ∈ Finset.range (d + 1),
    (((d + 1) / (d * unitBallVolume d) * Sg) ^ ((1 : ℝ) / (d + 1)) / r) ^ j)

/-- The square root of the variance of the radius is that of the sum over `d ω_d`. -/
private theorem sqrt_radiusVariance {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Real.sqrt (radiusVariance d ε) =
      (1 / (d * unitBallVolume d)) * Real.sqrt (sumVariance d ε) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hω := unitBallVolume_pos d
  rw [radiusVariance_eq hd hε, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (by positivity)]
  ring

/-- Almost surely the radius factor tends to `1 / (d ω_d)`. -/
private theorem ae_tendsto_radiusFactor {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → Site d)
    (hX : IsCERW μ ε X) {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
    (hrdef : ∀ n, r n = ((d + 1) * n / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1)))
    (hrpow : ∀ n, r n ^ (d + 1) = (d + 1) * n / (2 * d * ε * unitBallVolume d))
    (hmax : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, maxRadius (fun j => X j ω) n ≤ 2 * r n)
    (hQ2 : ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
      (∀ᶠ n : ℕ in atTop,
        σ * dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n
          ≤ (Real.sqrt (bracketLimit d ε) + δ) * Real.sqrt (2 * Real.log (Real.log n))) ∧
      (∃ᶠ n : ℕ in atTop,
        (Real.sqrt (bracketLimit d ε) - δ) * Real.sqrt (2 * Real.log (Real.log n))
          ≤ σ * dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      radiusFactor d (∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x) (r n)) atTop
      (𝓝 (1 / (d * unitBallVolume d))) := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hω := unitBallVolume_pos d
  filter_upwards [ae_sum_ratio hd hε μ X hX ha hr hrpow hmax hQ2] with ω h
  have hρ := tendsto_moment_ratio hd1 hε hrdef
    (Sg := fun n => ∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x)
    (fun n => Finset.sum_nonneg fun x _ => euclidNorm_nonneg x) h
  have hG : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (d + 1),
      (((d + 1) / (d * unitBallVolume d) * ∑ x ∈ departureRange (fun j => X j ω) n,
        euclidNorm x) ^ ((1 : ℝ) / (d + 1)) / r n) ^ j) atTop
      (𝓝 (∑ j ∈ Finset.range (d + 1), (1 : ℝ) ^ j)) :=
    tendsto_finsetSum _ fun j _ => hρ.pow j
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    Nat.cast_add, Nat.cast_one] at hG
  have hlim := (tendsto_const_nhds (x := ((d : ℝ) + 1))).div
    ((tendsto_const_nhds (x := (d : ℝ) * unitBallVolume d)).mul hG)
    (by positivity)
  have hval : ((d : ℝ) + 1) / ((d : ℝ) * unitBallVolume d * ((d : ℝ) + 1))
      = 1 / (d * unitBallVolume d) := by
    field_simp
  rw [hval] at hlim
  exact hlim

/-- The centered moment radius is the radius factor times the centered sum, for `n ≥ 1`. -/
private theorem momentRadius_eq_factor_mul {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ} (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
    (hrpow : ∀ n, r n ^ (d + 1) = (d + 1) * n / (2 * d * ε * unitBallVolume d))
    (Y : ℕ → Site d) (n : ℕ) (hn : n ≠ 0) :
    (momentRadius Y n - r n) / r n ^ ((3 - (d : ℝ)) / 2) =
      radiusFactor d (∑ x ∈ departureRange Y n, euclidNorm x) (r n) *
        ((∑ x ∈ departureRange Y n, euclidNorm x - n / (2 * ε)) /
          r n ^ (((d : ℝ) + 3) / 2)) :=
  moment_radius_identity hd hε (Finset.sum_nonneg fun x _ => euclidNorm_nonneg x) hn
    (scale_pos ha hr hn) (hrpow n)

/-- The central limit theorem for the moment radius. -/
private theorem radius_clt {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → Site d)
    (hX : IsCERW μ ε X) {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
    (hrpow : ∀ n, r n ^ (d + 1) = (d + 1) * n / (2 * d * ε * unitBallVolume d))
    (hS : TendstoInDistribution
      (fun n ω => (∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x - n / (2 * ε)) /
        r n ^ (((d : ℝ) + 3) / 2)) atTop id (fun _ => μ)
      (gaussianReal 0 (sumVariance d ε).toNNReal))
    (hA : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      radiusFactor d (∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x) (r n)) atTop
      (𝓝 (1 / (d * unitBallVolume d)))) :
    TendstoInDistribution
      (fun n ω => (momentRadius (fun j => X j ω) n - r n) / r n ^ ((3 - (d : ℝ)) / 2)) atTop id
      (fun _ => μ) (gaussianReal 0 (radiusVariance d ε).toNNReal) := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hω := unitBallVolume_pos d
  have hAmeas : ∀ n, Measurable (fun ω => radiusFactor d
      (∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x) (r n)) := fun n =>
    measurable_departureRange_fun hX.measurable n
      (fun A => radiusFactor d (∑ x ∈ A, euclidNorm x) (r n))
  have hRmeas : ∀ n, Measurable (fun ω =>
      (momentRadius (fun j => X j ω) n - r n) / r n ^ ((3 - (d : ℝ)) / 2)) := fun n =>
    measurable_departureRange_fun hX.measurable n
      (fun A => ((((d : ℝ) + 1) / (d * unitBallVolume d) * ∑ x ∈ A, euclidNorm x) ^
        ((1 : ℝ) / (d + 1)) - r n) / r n ^ ((3 - (d : ℝ)) / 2))
  have hAm : TendstoInMeasure μ (fun n ω => radiusFactor d
      (∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x) (r n)) atTop
      (fun _ => 1 / (d * unitBallVolume d)) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hAmeas n).aestronglyMeasurable) hA
  have hSl := hS.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ => p.2 * p.1) (by fun_prop) hAm (fun n => (hAmeas n).aemeasurable)
  have hv : 0 ≤ sumVariance d ε := by
    unfold sumVariance
    positivity
  have hT : TendstoInDistribution (fun n ω => radiusFactor d
        (∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x) (r n) *
      ((∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x - n / (2 * ε)) /
        r n ^ (((d : ℝ) + 3) / 2))) atTop id (fun _ => μ)
      (gaussianReal 0 (radiusVariance d ε).toNNReal) := by
    refine tendstoInDistribution_of_map_eq hSl measurable_id.aemeasurable ?_
    have h1 := gaussianReal_map_mul_toNNReal (1 / ((d : ℝ) * unitBallVolume d)) hv
    rw [radiusVariance_eq hd1 hε]
    simp only [Measure.map_id]
    convert h1 using 2
    · funext x
      simp [mul_comm]
    · congr 1
      field_simp
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hT ?_
    (fun n => (hRmeas n).aemeasurable)
  refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
  · exact ((hRmeas n).aemeasurable.sub (hT.forall_aemeasurable n)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp only [Pi.sub_apply]
    rw [momentRadius_eq_factor_mul hd1 hε ha hr hrpow (fun j => X j ω) n hn, sub_self]
    rfl

/-- The law of the iterated logarithm for the moment radius. -/
private theorem radius_lil {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → Ω → Site d)
    {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
    (hrpow : ∀ n, r n ^ (d + 1) = (d + 1) * n / (2 * d * ε * unitBallVolume d))
    (hS : ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
      (∀ᶠ n : ℕ in atTop,
        σ * ((∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x - n / (2 * ε)) /
          r n ^ (((d : ℝ) + 3) / 2))
          ≤ (Real.sqrt (sumVariance d ε) + δ) * Real.sqrt (2 * Real.log (Real.log n))) ∧
      (∃ᶠ n : ℕ in atTop,
        (Real.sqrt (sumVariance d ε) - δ) * Real.sqrt (2 * Real.log (Real.log n))
          ≤ σ * ((∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x - n / (2 * ε)) /
            r n ^ (((d : ℝ) + 3) / 2))))
    (hA : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      radiusFactor d (∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x) (r n)) atTop
      (𝓝 (1 / (d * unitBallVolume d)))) :
    ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
      (∀ᶠ n : ℕ in atTop,
        σ * ((momentRadius (fun j => X j ω) n - r n) / r n ^ ((3 - (d : ℝ)) / 2))
          ≤ (Real.sqrt (radiusVariance d ε) + δ) * Real.sqrt (2 * Real.log (Real.log n))) ∧
      (∃ᶠ n : ℕ in atTop,
        (Real.sqrt (radiusVariance d ε) - δ) * Real.sqrt (2 * Real.log (Real.log n))
          ≤ σ * ((momentRadius (fun j => X j ω) n - r n) / r n ^ ((3 - (d : ℝ)) / 2))) := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hω := unitBallVolume_pos d
  have hvpos : 0 < sumVariance d ε := by
    unfold sumVariance
    positivity
  have hloglogn : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hLtop : Tendsto (fun n : ℕ => Real.sqrt (2 * Real.log (Real.log n))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (hloglogn.const_mul_atTop two_pos)
  have hL : ∀ᶠ n : ℕ in atTop, 0 < Real.sqrt (2 * Real.log (Real.log n)) :=
    hLtop.eventually_gt_atTop 0
  filter_upwards [hS, hA] with ω hSω hAω δ hδ σ hσ
  have hmul := lil_mul_seq
    (a := fun n => σ * ((∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x - n / (2 * ε)) /
      r n ^ (((d : ℝ) + 3) / 2)))
    (A := fun n => radiusFactor d (∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x) (r n))
    (c := Real.sqrt (sumVariance d ε)) (κ := 1 / (d * unitBallVolume d))
    (Real.sqrt_pos.2 hvpos) (by positivity) hL hAω (fun δ' hδ' => hSω δ' hδ' σ hσ) δ hδ
  have hsq : Real.sqrt (radiusVariance d ε) =
      1 / (d * unitBallVolume d) * Real.sqrt (sumVariance d ε) := sqrt_radiusVariance hd1 hε
  have hid : ∀ n : ℕ, n ≠ 0 →
      σ * ((momentRadius (fun j => X j ω) n - r n) / r n ^ ((3 - (d : ℝ)) / 2))
        = radiusFactor d (∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x) (r n) *
          (σ * ((∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x - n / (2 * ε)) /
            r n ^ (((d : ℝ) + 3) / 2))) := by
    intro n hn
    rw [momentRadius_eq_factor_mul hd1 hε ha hr hrpow (fun j => X j ω) n hn]
    ring
  rw [hsq]
  refine ⟨?_, ?_⟩
  · filter_upwards [hmul.1, eventually_ne_atTop 0] with n hn hn0
    rw [hid n hn0]
    exact hn
  · refine (hmul.2.and_eventually (eventually_ne_atTop 0)).mono fun n ⟨hn, hn0⟩ => ?_
    rw [hid n hn0]
    exact hn

/-- A power of `log n` is eventually below any positive multiple of a positive power of `n`. -/
private theorem eventually_log_rpow_le {b c M K : ℝ} (hb : 0 ≤ b) (hc : 0 < c) (hM : 0 < M)
    (hK : 0 ≤ K) : ∀ᶠ n : ℕ in atTop, K * Real.log n ^ b ≤ M * (n : ℝ) ^ c := by
  have h := CERW.Support.Main.tendsto_log_rpow_div_rpow b hc
  have h2 : Tendsto (fun n : ℕ => K / M * (Real.log ((n : ℝ) + 2) ^ b / (n : ℝ) ^ c)) atTop
      (𝓝 0) := by
    simpa using h.const_mul (K / M)
  filter_upwards [h2.eventually (gt_mem_nhds one_pos), eventually_ge_atTop 1] with n h1 hn1
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn1
  have hlog : Real.log n ≤ Real.log ((n : ℝ) + 2) := Real.log_le_log hnpos (by linarith)
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have h3 : Real.log n ^ b ≤ Real.log ((n : ℝ) + 2) ^ b := Real.rpow_le_rpow hlog0 hlog hb
  have hcpos : 0 < (n : ℝ) ^ c := Real.rpow_pos_of_pos hnpos c
  have h4 : K / M * (Real.log ((n : ℝ) + 2) ^ b / (n : ℝ) ^ c)
      = K * Real.log ((n : ℝ) + 2) ^ b / (M * (n : ℝ) ^ c) := by
    field_simp
  rw [h4, div_lt_one (by positivity)] at h1
  calc K * Real.log n ^ b ≤ K * Real.log ((n : ℝ) + 2) ^ b :=
        mul_le_mul_of_nonneg_left h3 hK
    _ ≤ M * (n : ℝ) ^ c := h1.le

/-- The excess bound for the outer radius in the fluctuation theorem is eventually at most
`r_n`. -/
private theorem eventually_excess_le {d : ℕ} (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, (if d = 2 then C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)
      else C * Real.log n ^ ((d : ℝ) + 1)) ≤ r n := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  by_cases h2 : d = 2
  · simp only [if_pos h2]
    have hsqrt : ∀ n : ℕ, Real.sqrt (r n) =
        Real.sqrt a * (n : ℝ) ^ (((1 : ℝ) / (d + 1)) / 2) := fun n => by
      rw [hr n, Real.sqrt_mul ha.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
        ← Real.rpow_mul (Nat.cast_nonneg n)]
      rw [one_div (2 : ℝ), mul_comm]
      simp [div_eq_mul_inv]
      ring
    filter_upwards [eventually_log_rpow_le (b := (5 : ℝ) / 2)
      (c := ((1 : ℝ) / (d + 1)) / 2) (M := Real.sqrt a) (K := C) (by norm_num) (by positivity)
      (Real.sqrt_pos.2 ha) hC.le] with n hn
    have hrn : 0 ≤ r n := by
      rw [hr n]
      positivity
    calc C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)
        = Real.sqrt (r n) * (C * Real.log n ^ ((5 : ℝ) / 2)) := by ring
      _ ≤ Real.sqrt (r n) * (Real.sqrt a * (n : ℝ) ^ (((1 : ℝ) / (d + 1)) / 2)) :=
          mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _)
      _ = Real.sqrt (r n) * Real.sqrt (r n) := by rw [hsqrt n]
      _ = r n := Real.mul_self_sqrt hrn
  · simp only [if_neg h2]
    filter_upwards [eventually_log_rpow_le (b := (d : ℝ) + 1) (c := (1 : ℝ) / (d + 1))
      (M := a) (K := C) (by positivity) (by positivity) ha hC.le] with n hn
    rw [hr n]
    exact hn

/-- Theorem 8.1 of the paper: the central limit theorem and the law of the iterated logarithm for
the sum of the distances from the origin over the range and for the moment radius. -/
theorem moment_fluctuations_of (hshape : limit_shape.{u})
    (hfluct : fluctuation_rates.{u}) : moment_fluctuations.{u} := by
  intro d hd hCLT hLIL ωd ε hε hεd r v₁ v₂ Ω _ μ _ X hX S R
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hω : 0 < ωd := unitBallVolume_pos d
  have hc : 0 < ((d : ℝ) + 1) / (2 * d * ε * ωd) := by positivity
  set a : ℝ := (((d : ℝ) + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1)) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hc _
  have hr : ∀ n : ℕ, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := fun n => by
    show (((d : ℝ) + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1)) = _
    rw [show ((d : ℝ) + 1) * n / (2 * d * ε * ωd) =
      (((d : ℝ) + 1) / (2 * d * ε * ωd)) * n by ring]
    exact Real.mul_rpow hc.le (Nat.cast_nonneg n)
  have hrdef : ∀ n : ℕ, r n =
      ((d + 1) * n / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1)) := fun n => rfl
  have hrpow : ∀ n : ℕ, r n ^ (d + 1) = (d + 1) * n / (2 * d * ε * unitBallVolume d) :=
    fun n => by
    rw [hrdef n, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have : ((1 : ℝ) / (d + 1)) * ((d + 1 : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [this, Real.rpow_one]
  have hsh := hshape hd hε hεd μ X hX
  have hloc : ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ y : Site d,
      |(localTime (fun j => X j ω) n y : ℝ) - 2 * d * ε * max (r n - euclidNorm y) 0|
        ≤ η * r n := by
    filter_upwards [hsh] with ω h using h.2.1
  have hmax : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, maxRadius (fun j => X j ω) n ≤ 2 * r n := by
    obtain ⟨C, hC, -, hae⟩ := hfluct hd ε hε hεd 1 one_pos
    filter_upwards [hae μ X hX] with ω hω
    filter_upwards [hω, eventually_excess_le hd ha hr hC] with n hn hle
    have hex : maxRadius (fun j => X j ω) n - r n ≤ (if d = 2 then
        C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)
        else C * Real.log n ^ ((d : ℝ) + 1)) := by
      have h1 := hn.1
      by_cases h2 : d = 2
      · rw [if_pos h2] at h1 ⊢
        exact h1.2
      · rw [if_neg h2] at h1 ⊢
        exact h1.2
    linarith
  obtain ⟨hQ1, hQ2⟩ := dynkin_sq_laws hd hCLT hLIL hε hεd μ X hX ha hr hloc hmax
  have hSclt := sum_clt hd hε μ X hX ha hr hmax hQ1
  have hSlil := sum_lil hd hε μ X hX ha hr hmax hQ2
  have hAx := ae_tendsto_radiusFactor hd hε μ X hX ha hr hrdef hrpow hmax hQ2
  have hRclt := radius_clt hd hε μ X hX ha hr hrpow hSclt hAx
  have hRlil := radius_lil hd hε μ X ha hr hrpow hSlil hAx
  refine ⟨hSclt, hRclt, ?_⟩
  filter_upwards [hSlil, hRlil] with ω h1 h2 δ hδ σ hσ
  exact ⟨(h1 δ hδ σ hσ).1, (h1 δ hδ σ hσ).2, (h2 δ hδ σ hσ).1, (h2 δ hδ σ hσ).2⟩

end CERW.Support.Limit
