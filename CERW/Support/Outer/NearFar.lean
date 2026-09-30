import CERW.Support.Statements
import CERW.Support.Geometry.Bound

/-!
# The near and far parts of the positive potential

`lem:near-far`: for a measurable set `D` inside the annulus `{b ≤ |v| ≤ b + w}` whose caps
`D ∩ B((b+w)u, t)`, `t ≥ w`, have volume at most `λ t^{d-1}` and whose kernel integrals
`∫_D |v - y|^{2-d}` are at most `λ b`, the positive potential `U_D^+(y)` at a point of the annulus
is at most `C (λ w^{d-1})^{1/d} + C λ`.

The points of `D` within distance `w` of `y` are handled by the bathtub bound for `|v - y|^{1-d}`.
For the other points, the identity `2(|v|² - v·y) = |v - y|² + |v|² - |y|²` bounds the integrand by
`|v - y|² / (2b) + 3w/2` over `|v - y|^d`; the first term is controlled by the second hypothesis and
the second, summed over dyadic shells around `y`, by the cap bound.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer

open CERW.Support.Statements CERW CERW.Generic.Kernel CERW.Support.Geometry

variable {d : ℕ}

/-- The arithmetic of one dyadic shell: with `p = 2^k w`, the bound `M (2p)^{d-1} / p^d` equals
`2^d M / w / 2 / 2^k`. -/
private lemma shell_arith (hd : 1 ≤ d) {w : ℝ} (hw : 0 < w) (M : ℝ) (k : ℕ) :
    ((2 ^ k * w) ^ d)⁻¹ * (M * (2 ^ (k + 1) * w) ^ (d - 1)) = 2 ^ d * M / w / 2 / 2 ^ k := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have h2 : (2 : ℝ) ^ (k + 1) * w = 2 * (2 ^ k * w) := by ring
  generalize hpdef : (2 : ℝ) ^ k * w = p at h2
  have hp : 0 < p := hpdef ▸ by positivity
  rw [Nat.add_sub_cancel, h2, mul_pow, pow_succ p m, pow_succ (2 : ℝ) m]
  have hpm : 0 < p ^ m := by positivity
  rw [← hpdef]
  field_simp

/-- Dyadic shell estimate: if `|D ∩ B(y, t)| ≤ M t^{d-1}` for every `t ≥ w`, then the integral of
`|v - y|^{-d}` over `D` outside `B(y, w)` is at most `2^d M / w`. -/
private lemma lintegral_far_le (hd : 1 ≤ d) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) (y : EuclideanSpace ℝ (Fin d)) {w M : ℝ} (hw : 0 < w)
    (hM : 0 ≤ M)
    (hcap : ∀ t : ℝ, w ≤ t → volume (D ∩ Metric.ball y t) ≤ ENNReal.ofReal (M * t ^ (d - 1))) :
    ∫⁻ v in D \ Metric.ball y w, ENNReal.ofReal ((‖v - y‖ ^ d)⁻¹)
      ≤ ENNReal.ofReal (2 ^ d * M / w) := by
  set S : ℕ → Set (EuclideanSpace ℝ (Fin d)) := fun k =>
    D ∩ (Metric.ball y (2 ^ (k + 1) * w) \ Metric.ball y (2 ^ k * w)) with hS
  have hcover : D \ Metric.ball y w ⊆ ⋃ k, S k := by
    intro v hv
    have hr : w ≤ ‖v - y‖ := by
      have := hv.2
      rwa [mem_ball_iff_norm, not_lt] at this
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (x := ‖v - y‖ / w) (y := (2 : ℝ))
      ((one_le_div hw).mpr hr) (by norm_num)
    rw [le_div_iff₀ hw] at hk1
    rw [div_lt_iff₀ hw] at hk2
    refine Set.mem_iUnion.mpr ⟨k, hv.1, ?_, ?_⟩
    · rw [mem_ball_iff_norm]
      exact hk2
    · rw [mem_ball_iff_norm, not_lt]
      exact hk1
  have hshell : ∀ k : ℕ, ∫⁻ v in S k, ENNReal.ofReal ((‖v - y‖ ^ d)⁻¹)
      ≤ ENNReal.ofReal (2 ^ d * M / w / 2 / 2 ^ k) := by
    intro k
    have hpk : 0 < (2 : ℝ) ^ k * w := by positivity
    have hSm : MeasurableSet (S k) :=
      hD.inter (Metric.isOpen_ball.measurableSet.diff Metric.isOpen_ball.measurableSet)
    have hle : ∫⁻ v in S k, ENNReal.ofReal ((‖v - y‖ ^ d)⁻¹)
        ≤ ∫⁻ _ in S k, ENNReal.ofReal (((2 ^ k * w) ^ d)⁻¹) := by
      refine setLIntegral_mono' hSm fun v hv => ?_
      have hv' : 2 ^ k * w ≤ ‖v - y‖ := by
        have := hv.2.2
        rwa [mem_ball_iff_norm, not_lt] at this
      exact ENNReal.ofReal_le_ofReal
        (inv_anti₀ (pow_pos hpk d) (pow_le_pow_left₀ hpk.le hv' d))
    have hvol : volume (S k) ≤ ENNReal.ofReal (M * (2 ^ (k + 1) * w) ^ (d - 1)) := by
      refine le_trans (measure_mono ?_) (hcap _ ?_)
      · exact Set.inter_subset_inter_right _ Set.sdiff_subset
      · exact le_mul_of_one_le_left hw.le (one_le_pow₀ (by norm_num))
    rw [setLIntegral_const] at hle
    refine hle.trans ?_
    calc ENNReal.ofReal (((2 ^ k * w) ^ d)⁻¹) * volume (S k)
        ≤ ENNReal.ofReal (((2 ^ k * w) ^ d)⁻¹)
            * ENNReal.ofReal (M * (2 ^ (k + 1) * w) ^ (d - 1)) :=
          mul_le_mul_right hvol _
      _ = ENNReal.ofReal (((2 ^ k * w) ^ d)⁻¹ * (M * (2 ^ (k + 1) * w) ^ (d - 1))) :=
          (ENNReal.ofReal_mul (inv_nonneg.mpr (pow_pos hpk d).le)).symm
      _ = ENNReal.ofReal (2 ^ d * M / w / 2 / 2 ^ k) := by rw [shell_arith hd hw]
  calc ∫⁻ v in D \ Metric.ball y w, ENNReal.ofReal ((‖v - y‖ ^ d)⁻¹)
      ≤ ∫⁻ v in ⋃ k, S k, ENNReal.ofReal ((‖v - y‖ ^ d)⁻¹) := lintegral_mono_set hcover
    _ ≤ ∑' k, ∫⁻ v in S k, ENNReal.ofReal ((‖v - y‖ ^ d)⁻¹) := lintegral_iUnion_le _ _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (2 ^ d * M / w / 2 / 2 ^ k) := ENNReal.tsum_le_tsum hshell
    _ = ENNReal.ofReal (2 ^ d * M / w) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
            (summable_geometric_two' _), tsum_geometric_two']

/-- Between the two radii, the radial component of the direction of `v` along `v - y` is at most
`|v - y|² / (2b) + 3w/2`: this is the identity `2(|v|² - v·y) = |v - y|² + |v|² - |y|²`
together with `|v|² - |y|² ≤ 3bw`. -/
private lemma inner_unitDir_le {b w : ℝ} (hw : 0 < w) (hwb : w ≤ b)
    {v y : EuclideanSpace ℝ (Fin d)} (hv : b ≤ ‖v‖) (hv' : ‖v‖ ≤ b + w) (hy : b ≤ ‖y‖) :
    inner ℝ (unitDir v) (v - y) ≤ ‖v - y‖ ^ 2 / (2 * b) + 3 * w / 2 := by
  have hb : 0 < b := hw.trans_le hwb
  have hvpos : 0 < ‖v‖ := hb.trans_le hv
  have hid : 2 * inner ℝ v (v - y) = ‖v - y‖ ^ 2 + (‖v‖ ^ 2 - ‖y‖ ^ 2) := by
    rw [norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq]
    ring
  have h1 : ‖v‖ ^ 2 ≤ (b + w) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv' 2
  have h2 : b ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ hb.le hy 2
  have h3 : w * w ≤ b * w := mul_le_mul_of_nonneg_right hwb hw.le
  have hX : inner ℝ v (v - y) ≤ (‖v - y‖ ^ 2 + 3 * b * w) / 2 := by
    have : ‖v‖ ^ 2 - ‖y‖ ^ 2 ≤ 3 * b * w := by linarith
    linarith
  have hnn : 0 ≤ (‖v - y‖ ^ 2 + 3 * b * w) / 2 := by positivity
  calc inner ℝ (unitDir v) (v - y) = ‖v‖⁻¹ * inner ℝ v (v - y) := by
        rw [unitDir, real_inner_smul_left]
    _ ≤ ‖v‖⁻¹ * ((‖v - y‖ ^ 2 + 3 * b * w) / 2) :=
        mul_le_mul_of_nonneg_left hX (inv_nonneg.mpr hvpos.le)
    _ ≤ b⁻¹ * ((‖v - y‖ ^ 2 + 3 * b * w) / 2) :=
        mul_le_mul_of_nonneg_right (inv_anti₀ hb hv) hnn
    _ = ‖v - y‖ ^ 2 / (2 * b) + 3 * w / 2 := by field_simp

/-- Outside `B(y, w)`, between the two radii, the positive part of the potential integrand is at
most `|v - y|^{2-d} / (2b) + (3w/2) |v - y|^{-d}`. -/
private lemma integrand_far_le {b w : ℝ} (hw : 0 < w) (hwb : w ≤ b)
    {v y : EuclideanSpace ℝ (Fin d)} (hv : b ≤ ‖v‖) (hv' : ‖v‖ ≤ b + w) (hy : b ≤ ‖y‖)
    (hvy : w ≤ ‖v - y‖) :
    max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0
      ≤ 1 / (2 * b) * ‖v - y‖ ^ (2 - (d : ℝ)) + 3 * w / 2 * (‖v - y‖ ^ d)⁻¹ := by
  have hb : 0 < b := hw.trans_le hwb
  have hr : 0 < ‖v - y‖ := hw.trans_le hvy
  have hrd : 0 < ‖v - y‖ ^ d := pow_pos hr d
  have hrpow : ‖v - y‖ ^ (2 - (d : ℝ)) = ‖v - y‖ ^ 2 / ‖v - y‖ ^ d := by
    rw [Real.rpow_sub hr, Real.rpow_two, Real.rpow_natCast]
  have hrhs : 1 / (2 * b) * ‖v - y‖ ^ (2 - (d : ℝ)) + 3 * w / 2 * (‖v - y‖ ^ d)⁻¹
      = (‖v - y‖ ^ 2 / (2 * b) + 3 * w / 2) / ‖v - y‖ ^ d := by
    rw [hrpow]
    field_simp
  rw [hrhs]
  refine max_le (div_le_div_of_nonneg_right (inner_unitDir_le hw hwb hv hv' hy) hrd.le) ?_
  positivity

/-- The Newtonian weight `|v - y|^{2-d}` is integrable on a measurable set of finite volume on
which `|v - y| ≤ R`. -/
private lemma integrableOn_rpow_two_sub (hd : 2 ≤ d) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤) (y : EuclideanSpace ℝ (Fin d)) {R : ℝ}
    (hR : ∀ v ∈ D, ‖v - y‖ ≤ R) :
    IntegrableOn (fun v => ‖v - y‖ ^ (2 - (d : ℝ))) D := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨hint, _⟩ := integrableOn_and_setIntegral_le (d := d) (by omega) hD hDfin y
  have hmeas : Measurable (fun v : EuclideanSpace ℝ (Fin d) => ‖v - y‖ ^ (2 - (d : ℝ))) :=
    (measurable_norm.comp (measurable_id.sub_const y)).pow_const _
  refine (hint.const_mul R).mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hD, ae_restrict_of_ae (Measure.ae_ne volume y)]
    with v hvD hne
  have hr : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hsplit : ‖v - y‖ ^ (2 - (d : ℝ)) = ‖v - y‖ ^ (1 - (d : ℝ)) * ‖v - y‖ := by
    rw [show (2 : ℝ) - d = (1 - d) + 1 by ring, Real.rpow_add hr, Real.rpow_one]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hr.le _), hsplit, mul_comm R]
  exact mul_le_mul_of_nonneg_left (hR v hvD) (Real.rpow_nonneg hr.le _)

/-- A nonzero vector has direction of norm one. -/
private lemma norm_unitDir_of_ne {y : EuclideanSpace ℝ (Fin d)} (hy : y ≠ 0) :
    ‖unitDir y‖ = 1 := by
  rw [unitDir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]

/-- For `b ≤ |y| ≤ b + w` and `t ≥ w`, the ball `B(y, t)` lies in the ball of radius `2t` about
the point of the outer sphere nearest to `y`. -/
private lemma ball_subset_cap {b w : ℝ} {y : EuclideanSpace ℝ (Fin d)} (hy : b ≤ ‖y‖)
    (hy' : ‖y‖ ≤ b + w) (hy0 : y ≠ 0) {t : ℝ} (ht : w ≤ t) :
    Metric.ball y t ⊆ Metric.ball ((b + w) • unitDir y) (2 * t) := by
  intro v hv
  rw [mem_ball_iff_norm] at hv ⊢
  have hu := norm_unitDir_of_ne hy0
  have hyu : y = ‖y‖ • unitDir y := by
    rw [unitDir, smul_inv_smul₀ (norm_ne_zero_iff.mpr hy0)]
  have hdist : ‖y - (b + w) • unitDir y‖ ≤ w := by
    have : y - (b + w) • unitDir y = (‖y‖ - (b + w)) • unitDir y := by
      rw [sub_smul, ← hyu]
    rw [this, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  calc ‖v - (b + w) • unitDir y‖ = ‖(v - y) + (y - (b + w) • unitDir y)‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖v - y‖ + ‖y - (b + w) • unitDir y‖ := norm_add_le _ _
    _ < 2 * t := by linarith

theorem near_far_holds : near_far := by
  intro d hd ε hε _
  have hd1 : 1 ≤ d := by omega
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = d * unitBallVolume d
      * (2 ^ (d - 1) / unitBallVolume d) ^ ((1 : ℝ) / d) := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, K₂ = 1 / 2 + 3 / 2 * 2 ^ d * 2 ^ (d - 1) := ⟨_, rfl⟩
  have hK₁pos : 0 < K₁ := by
    rw [hK₁]
    have : (0 : ℝ) < d := by exact_mod_cast hd1
    positivity
  have hK₂pos : 0 < K₂ := by rw [hK₂]; positivity
  refine ⟨2 * ε / unitBallVolume d * (K₁ + K₂), by positivity, ?_⟩
  intro w b lam hw hwb hlam D hD hDsub hcap hint y hyb hyb'
  have hb : 0 < b := by linarith
  have hwpos : 0 < w := by linarith
  have hlam0 : 0 < lam := by linarith
  have hy0 : y ≠ 0 := norm_pos_iff.mp (by linarith)
  have hDball : D ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (b + w) :=
    fun v hv => mem_closedBall_zero_iff.mpr (hDsub hv).2
  have hDfin : volume D ≠ ⊤ :=
    ((measure_mono hDball).trans_lt measure_closedBall_lt_top).ne
  have hcap' : ∀ t : ℝ, w ≤ t →
      volume (D ∩ Metric.ball y t) ≤ ENNReal.ofReal (2 ^ (d - 1) * lam * t ^ (d - 1)) := by
    intro t ht
    calc volume (D ∩ Metric.ball y t)
        ≤ volume (D ∩ Metric.ball ((b + w) • unitDir y) (2 * t)) :=
          measure_mono (Set.inter_subset_inter_right _ (ball_subset_cap hyb hyb' hy0 ht))
      _ ≤ ENNReal.ofReal (lam * (2 * t) ^ (d - 1)) :=
          hcap _ (norm_unitDir_of_ne hy0) _ (by linarith)
      _ = ENNReal.ofReal (2 ^ (d - 1) * lam * t ^ (d - 1)) := by
          rw [mul_pow]
          congr 1
          ring
  have hmeasf : Measurable (fun v : EuclideanSpace ℝ (Fin d) =>
      max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0) := by
    have hdir : Measurable (fun v : EuclideanSpace ℝ (Fin d) => unitDir v) := by
      change Measurable (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖⁻¹ • v)
      fun_prop
    have hsub : Measurable (fun v : EuclideanSpace ℝ (Fin d) => v - y) :=
      measurable_id.sub measurable_const
    exact ((hdir.inner hsub).div (hsub.norm.pow_const d)).max measurable_const
  have hBm : MeasurableSet (Metric.ball y w) := Metric.isOpen_ball.measurableSet
  have hnear : ∫⁻ v in D ∩ Metric.ball y w,
      ENNReal.ofReal (max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0)
      ≤ ENNReal.ofReal (K₁ * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d)) := by
    have hfin' : volume (D ∩ Metric.ball y w) ≠ ⊤ :=
      measure_ne_top_of_subset Set.inter_subset_left hDfin
    obtain ⟨hint1, hle1⟩ := integrableOn_and_setIntegral_le hd1 (hD.inter hBm) hfin' y
    have hV : (volume (D ∩ Metric.ball y w)).toReal ≤ 2 ^ (d - 1) * lam * w ^ (d - 1) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hcap' w le_rfl)
    calc ∫⁻ v in D ∩ Metric.ball y w,
          ENNReal.ofReal (max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0)
        ≤ ∫⁻ v in D ∩ Metric.ball y w, ENNReal.ofReal (‖v - y‖ ^ (1 - (d : ℝ))) :=
          setLIntegral_mono' (hD.inter hBm) fun v _ => ENNReal.ofReal_le_ofReal
            (max_le ((le_abs_self _).trans (abs_potentialIntegrand_le v y))
              (Real.rpow_nonneg (norm_nonneg _) _))
      _ = ENNReal.ofReal (∫ v in D ∩ Metric.ball y w, ‖v - y‖ ^ (1 - (d : ℝ))) :=
          (ofReal_integral_eq_lintegral_ofReal hint1
            (Filter.Eventually.of_forall fun v => Real.rpow_nonneg (norm_nonneg _) _)).symm
      _ ≤ ENNReal.ofReal (d * unitBallVolume d
            * ((volume (D ∩ Metric.ball y w)).toReal / unitBallVolume d) ^ ((1 : ℝ) / d)) :=
          ENNReal.ofReal_le_ofReal hle1
      _ ≤ ENNReal.ofReal (K₁ * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          have hpow : ((volume (D ∩ Metric.ball y w)).toReal / unitBallVolume d) ^ ((1 : ℝ) / d)
              ≤ (2 ^ (d - 1) / unitBallVolume d) ^ ((1 : ℝ) / d)
                * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d) := by
            rw [← Real.mul_rpow (by positivity) (by positivity)]
            refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
            calc (volume (D ∩ Metric.ball y w)).toReal / unitBallVolume d
                ≤ 2 ^ (d - 1) * lam * w ^ (d - 1) / unitBallVolume d :=
                  div_le_div_of_nonneg_right hV hω.le
              _ = 2 ^ (d - 1) / unitBallVolume d * (lam * w ^ (d - 1)) := by ring
          calc d * unitBallVolume d
                * ((volume (D ∩ Metric.ball y w)).toReal / unitBallVolume d) ^ ((1 : ℝ) / d)
              ≤ d * unitBallVolume d * ((2 ^ (d - 1) / unitBallVolume d) ^ ((1 : ℝ) / d)
                * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d)) :=
                mul_le_mul_of_nonneg_left hpow (by positivity)
            _ = K₁ * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d) := by rw [hK₁]; ring
  have hsubm : Measurable (fun v : EuclideanSpace ℝ (Fin d) => ‖v - y‖) :=
    measurable_norm.comp (measurable_id.sub_const y)
  have hg2 : ∫⁻ v in D, ENNReal.ofReal (1 / (2 * b) * ‖v - y‖ ^ (2 - (d : ℝ)))
      ≤ ENNReal.ofReal (lam / 2) := by
    have hR : ∀ v ∈ D, ‖v - y‖ ≤ 2 * (b + w) := fun v hv =>
      calc ‖v - y‖ ≤ ‖v‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ 2 * (b + w) := by linarith [(hDsub hv).2]
    have hint2 := (integrableOn_rpow_two_sub hd hD hDfin y hR).const_mul (1 / (2 * b))
    rw [← ofReal_integral_eq_lintegral_ofReal hint2
      (Filter.Eventually.of_forall fun v => by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_const_mul]
    calc 1 / (2 * b) * ∫ v in D, ‖v - y‖ ^ (2 - (d : ℝ)) ≤ 1 / (2 * b) * (lam * b) :=
          mul_le_mul_of_nonneg_left (hint y) (by positivity)
      _ = lam / 2 := by field_simp
  have hg3 : ∫⁻ v in D \ Metric.ball y w, ENNReal.ofReal (3 * w / 2 * (‖v - y‖ ^ d)⁻¹)
      ≤ ENNReal.ofReal (3 / 2 * 2 ^ d * 2 ^ (d - 1) * lam) := by
    have hfar := lintegral_far_le hd1 hD y hwpos (by positivity) hcap'
    have hmeas3 : Measurable (fun v : EuclideanSpace ℝ (Fin d) =>
        ENNReal.ofReal ((‖v - y‖ ^ d)⁻¹)) :=
      ENNReal.measurable_ofReal.comp (hsubm.pow_const d).inv
    calc ∫⁻ v in D \ Metric.ball y w, ENNReal.ofReal (3 * w / 2 * (‖v - y‖ ^ d)⁻¹)
        = ENNReal.ofReal (3 * w / 2)
            * ∫⁻ v in D \ Metric.ball y w, ENNReal.ofReal ((‖v - y‖ ^ d)⁻¹) := by
          rw [← lintegral_const_mul _ hmeas3]
          refine lintegral_congr fun v => ?_
          exact ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal (3 * w / 2) * ENNReal.ofReal (2 ^ d * (2 ^ (d - 1) * lam) / w) :=
          mul_le_mul_right hfar _
      _ = ENNReal.ofReal (3 / 2 * 2 ^ d * 2 ^ (d - 1) * lam) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  have hfar : ∫⁻ v in D \ Metric.ball y w,
      ENNReal.ofReal (max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0)
      ≤ ENNReal.ofReal (K₂ * lam) := by
    have hpt : ∀ v ∈ D \ Metric.ball y w,
        ENNReal.ofReal (max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0)
        ≤ ENNReal.ofReal (1 / (2 * b) * ‖v - y‖ ^ (2 - (d : ℝ)))
          + ENNReal.ofReal (3 * w / 2 * (‖v - y‖ ^ d)⁻¹) := by
      intro v hv
      have hvy : w ≤ ‖v - y‖ := by
        have := hv.2
        rwa [mem_ball_iff_norm, not_lt] at this
      obtain ⟨hv1, hv2⟩ := hDsub hv.1
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (integrand_far_le hwpos hwb hv1 hv2 hyb hvy)
    have hmeas2 : Measurable (fun v : EuclideanSpace ℝ (Fin d) =>
        ENNReal.ofReal (1 / (2 * b) * ‖v - y‖ ^ (2 - (d : ℝ)))) :=
      ENNReal.measurable_ofReal.comp ((hsubm.pow_const _).const_mul _)
    calc ∫⁻ v in D \ Metric.ball y w,
          ENNReal.ofReal (max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0)
        ≤ ∫⁻ v in D \ Metric.ball y w, (ENNReal.ofReal (1 / (2 * b) * ‖v - y‖ ^ (2 - (d : ℝ)))
            + ENNReal.ofReal (3 * w / 2 * (‖v - y‖ ^ d)⁻¹)) :=
          setLIntegral_mono' (hD.diff hBm) hpt
      _ = (∫⁻ v in D \ Metric.ball y w, ENNReal.ofReal (1 / (2 * b) * ‖v - y‖ ^ (2 - (d : ℝ))))
          + ∫⁻ v in D \ Metric.ball y w, ENNReal.ofReal (3 * w / 2 * (‖v - y‖ ^ d)⁻¹) :=
          lintegral_add_left hmeas2 _
      _ ≤ ENNReal.ofReal (lam / 2) + ENNReal.ofReal (3 / 2 * 2 ^ d * 2 ^ (d - 1) * lam) :=
          add_le_add ((lintegral_mono_set Set.sdiff_subset).trans hg2) hg3
      _ = ENNReal.ofReal (K₂ * lam) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), hK₂]
          congr 1
          ring
  have key : ∫ v in D, max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0
      ≤ K₁ * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d) + K₂ * lam := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (f := fun v : EuclideanSpace ℝ (Fin d) =>
        max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0)
      (Filter.Eventually.of_forall fun v => le_max_right _ _) hmeasf.aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    rw [← lintegral_inter_add_sdiff _ D hBm]
    refine (add_le_add hnear hfar).trans_eq ?_
    exact (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  have hX : 0 ≤ (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d) := by positivity
  rw [positivePotential]
  calc 2 * ε / unitBallVolume d * ∫ v in D, max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0
      ≤ 2 * ε / unitBallVolume d * (K₁ * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d) + K₂ * lam) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ ≤ 2 * ε / unitBallVolume d * ((K₁ + K₂) * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d)
          + (K₁ + K₂) * lam) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h1 : K₁ * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d)
            ≤ (K₁ + K₂) * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d) :=
          mul_le_mul_of_nonneg_right (by linarith) hX
        have h2 : K₂ * lam ≤ (K₁ + K₂) * lam := mul_le_mul_of_nonneg_right (by linarith) hlam0.le
        linarith
    _ = 2 * ε / unitBallVolume d * (K₁ + K₂) * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d)
          + 2 * ε / unitBallVolume d * (K₁ + K₂) * lam := by ring

end CERW.Support.Outer
