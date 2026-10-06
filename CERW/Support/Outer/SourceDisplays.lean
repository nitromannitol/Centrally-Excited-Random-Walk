import CERW.Support.Outer.OuterRadius
import CERW.Frozen.InnerRadius
import CERW.Support.Law.Existence

/-!
# The full displayed assertions of the inner- and outer-radius sections

Sections 6 and 7 display several intermediate assertions in a wider form than the estimates that
the proofs of `prop:inner` and `prop:stronger-outer` consume. This module proves the displays
themselves, for the actual objects of the paper: the potential `U_D`, its positive part `U_D^+`,
the weight `χ(ζ) = (1 + |ζ|)^{2-2d}`, the cells of the range, the local time `ℓ_n` and the
bracket `W_x`.

* `potential_convolution` is `eq:potential-convolution`: for `d ≥ 3`, every bounded measurable
  set `D` that contains a ball `B(0,b)` and **every** point `y`,
  `(χ * U_D)(y) ≤ ‖χ‖₁ (U_{B(0,b)}(y) + min {U_E^+(y), sup |U_E|}) + C log n`, `E = D ∖ B(0,b)`.
  The two bounds on `χ * U_E` that precede it are `convolution_potential_le_positivePotential`
  (`(χ * U_E)(y) ≤ ‖χ‖₁ U_E^+(y)`) and `abs_convolution_potential_le_supAbs`
  (`|(χ * U_E)(y)| ≤ ‖χ‖₁ sup |U_E|`); `potential_convolution_cellSet` is the form for the range
  of a path, with no bound on `b` assumed.
* `envelope_high_full` is `eq:envelopehigh` at **every** point: the bound
  `ℓ~_n(y) ≤ C ((b - |y|)_+ + sup |U_E| + log n)` and, for `|y| ≥ b`, the bound
  `ℓ~_n(y) ≤ C (U_E^+(y) + log n)`. `envelope_high_prob` applies both displays to the inner
  radius `b = R_in(n)` with probability at least `1 - C n^{-p}`, and
  `exists_realization_envelope_high` consumes them at an actual walk.
* `layer_cake_eq` is the identity `∫_E |v - y|^{2-d} dv = (d - 2) ∫_0^∞ |E ∩ B(y,t)| t^{1-d} dt`
  for `d ≥ 3`, every bounded measurable `E` and every point `y`, with both sides finite.
* `global_approximation_scale` is `eq:global` at the exact scale `√r_n log n` (`d = 2`) and
  `√(r_n log n)` (`d ≥ 3`). `planar_envelope_all_points` is the planar envelope
  `ℓ~_n(y) ≤ 2dε (b - |y|)_+ + C r_n^{3/4} (log n)^{1/4}` at every `y`, and
  `planar_localtime_all_sites` is `ℓ_n(x) ≤ 2dε (b - |x|)_+ + C w + C √r_n log n` at every site
  `x`; each has a probability version and `exists_realization_planar_displays` consumes them.
* `harmonicOnNhd_planar_potential` and `harmonicAt_planar_newton_field` state that, in the plane,
  the potential of a set outside a disc is harmonic inside the disc and that each coordinate of
  the Newton field is harmonic off its singularity.

No display is assumed. The deterministic statements take only clauses of the good event of the
paper (the approximation of the local time by the potential with its bracket, a path from the
origin with unit steps) or the clauses of `prop:inner`; the probability statements discharge
them with the proved producers.
-/

universe u

open MeasureTheory Filter Topology
open scoped symmDiff
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.SourceDisplays

open CERW CERW.Support.Statements
open private NewtonConv newton_conv ev_chi ev_chi_nonneg ev_chi_norm ev_integrable_chi_norm
  ev_integrable_chi_mul_potential ev_potential_split ev_potential_le_positivePotential
  ev_positivePotential_nonneg ev_integral_chi_mul_min_le ev_cellWeight ev_sum_setIntegral_mul_le
  ev_neg_le_potential_of_not_mem ev_log_one_add_max_le ev_kernel_sum_le ev_maxRadius_le_nat
  ev_braSum_eq ev_kern braSum co_log_add_two_le gma_integrableOn_rpow gmb_lintegral_tail
  PathFacts PathFacts.mk exists_pathFacts_prob ball_innerRadius_subset innerRadius_nonneg
  one_le_ofReal_mul_rpow gd_maxRadius_nonneg
  from CERW.Support.Outer.OuterRadius

variable {d : ℕ}

/-! ## The layer-cake identity -/

/-- The layer-cake formula in `[0, ∞]`: for every measurable `E` and every point `y`, the integral
of `|v - y|^{2-d}` over `E` equals `∫ (d - 2) t^{1-d} |E ∩ B(y,t)| dt`. The singular point
`v = y`, where the integrand reads `0` and the inner integral diverges, is a null set. -/
private lemma layer_cake_lintegral (hd : 3 ≤ d) {E : Set (EuclideanSpace ℝ (Fin d))}
    (hE : MeasurableSet E) (y : EuclideanSpace ℝ (Fin d)) :
    ∫⁻ v in E, ENNReal.ofReal (‖v - y‖ ^ (2 - (d : ℝ))) =
      ∫⁻ t, ENNReal.ofReal (((d : ℝ) - 2) * t ^ (1 - (d : ℝ))) *
        volume (E ∩ Metric.ball y t) := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set f : ℝ → ENNReal := fun t => ENNReal.ofReal (((d : ℝ) - 2) * t ^ (1 - (d : ℝ))) with hf
  have hfm : Measurable f := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact measurable_const.mul (measurable_id.pow_const _)
  set G : EuclideanSpace ℝ (Fin d) → ℝ → ENNReal :=
    fun v t => if ‖v - y‖ < t then f t else 0 with hG
  have hGm : Measurable (Function.uncurry G) := by
    have hS : MeasurableSet {q : EuclideanSpace ℝ (Fin d) × ℝ | ‖q.1 - y‖ < q.2} :=
      measurableSet_lt ((measurable_fst.sub_const y).norm) measurable_snd
    exact Measurable.ite hS (hfm.comp measurable_snd) measurable_const
  have h1 : ∀ v, v ≠ y → ENNReal.ofReal (‖v - y‖ ^ (2 - (d : ℝ))) = ∫⁻ t, G v t := by
    intro v hv
    have hr : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv)
    have hvt : (fun t => G v t) = (Set.Ioi ‖v - y‖).indicator f := by
      funext t
      simp [hG, Set.indicator]
    rw [hvt, lintegral_indicator measurableSet_Ioi, hf, gmb_lintegral_tail hd hr]
  have hae : ∀ᵐ v ∂(volume.restrict E), v ≠ y := by
    filter_upwards [ae_restrict_of_ae ((Set.countable_singleton y).ae_notMem
      (volume : Measure (EuclideanSpace ℝ (Fin d))))] with v hv
    simpa using hv
  calc ∫⁻ v in E, ENNReal.ofReal (‖v - y‖ ^ (2 - (d : ℝ)))
      = ∫⁻ v in E, ∫⁻ t, G v t := lintegral_congr_ae (hae.mono h1)
    _ = ∫⁻ t, ∫⁻ v in E, G v t := lintegral_lintegral_swap hGm.aemeasurable
    _ = ∫⁻ t, f t * volume (E ∩ Metric.ball y t) := by
        congr 1
        funext t
        have hvt : (fun v => G v t) = (Metric.ball y t).indicator (fun _ => f t) := by
          funext v
          simp [hG, Set.indicator, dist_eq_norm]
        rw [hvt, lintegral_indicator_const Metric.isOpen_ball.measurableSet,
          Measure.restrict_apply' hE, Set.inter_comm]

/-- **The layer-cake identity** (`eq:layer-cake`, Section 7). For `d ≥ 3`, a bounded measurable
set `E ⊂ ℝ^d` and a point `y ∈ ℝ^d`, both sides are finite and
`∫_E |v - y|^{2-d} dv = (d - 2) ∫_0^∞ |E ∩ B(y,t)| t^{1-d} dt`, where `B(y,t)` is the open ball.
The point `v = y` is a null set and is accounted for in the proof; the function
`t ↦ |E ∩ B(y,t)| t^{1-d}` is integrable on `(0, ∞)`. -/
theorem layer_cake_eq (hd : 3 ≤ d) {E : Set (EuclideanSpace ℝ (Fin d))}
    (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) (y : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v - y‖ ^ (2 - (d : ℝ))) E ∧
      IntegrableOn (fun t : ℝ => (volume (E ∩ Metric.ball y t)).toReal * t ^ (1 - (d : ℝ)))
        (Set.Ioi 0) ∧
      ∫ v in E, ‖v - y‖ ^ (2 - (d : ℝ)) =
        ((d : ℝ) - 2) * ∫ t in Set.Ioi (0 : ℝ),
          (volume (E ∩ Metric.ball y t)).toReal * t ^ (1 - (d : ℝ)) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 0 < (d : ℝ) - 2 := by linarith
  have hint := gma_integrableOn_rpow (by omega : 2 ≤ d) hEb y
  have hL := layer_cake_lintegral hd hE y
  set F : ℝ → ENNReal := fun t => ENNReal.ofReal (((d : ℝ) - 2) * t ^ (1 - (d : ℝ))) *
    volume (E ∩ Metric.ball y t) with hF
  have hvolfin : ∀ t : ℝ, volume (E ∩ Metric.ball y t) ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.inter_subset_right)
  have hFnonpos : ∀ t : ℝ, t ≤ 0 → F t = 0 := by
    intro t ht
    have : Metric.ball y t = ∅ := Metric.ball_eq_empty.mpr ht
    simp [hF, this]
  have hFpos : ∀ t : ℝ, 0 < t → (F t).toReal =
      ((d : ℝ) - 2) * ((volume (E ∩ Metric.ball y t)).toReal * t ^ (1 - (d : ℝ))) := by
    intro t ht
    simp only [hF]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (mul_nonneg hp.le (Real.rpow_nonneg ht.le _))]
    ring
  have hFm : Measurable F := by
    have h1 : Measurable fun t : ℝ => ENNReal.ofReal (((d : ℝ) - 2) * t ^ (1 - (d : ℝ))) := by
      refine ENNReal.measurable_ofReal.comp ?_
      exact measurable_const.mul (measurable_id.pow_const _)
    have h2 : Monotone fun t : ℝ => volume (E ∩ Metric.ball y t) := fun s t hst =>
      measure_mono (Set.inter_subset_inter_right _ (Metric.ball_subset_ball hst))
    exact h1.mul h2.measurable
  have hlt : ∫⁻ t, F t ≠ ⊤ := by
    rw [hF, ← hL]
    exact hint.lintegral_lt_top.ne
  have hFint : Integrable (fun t => (F t).toReal) :=
    integrable_toReal_of_lintegral_ne_top hFm.aemeasurable hlt
  have hg : IntegrableOn (fun t : ℝ => (volume (E ∩ Metric.ball y t)).toReal *
      t ^ (1 - (d : ℝ))) (Set.Ioi 0) := by
    have h1 : IntegrableOn (fun t : ℝ => (1 / ((d : ℝ) - 2)) * (F t).toReal) (Set.Ioi 0) :=
      hFint.integrableOn.const_mul _
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
    beta_reduce
    rw [hFpos t ht]
    field_simp
  refine ⟨hint, hg, ?_⟩
  have hnn : 0 ≤ᵐ[volume.restrict E] fun v : EuclideanSpace ℝ (Fin d) =>
      ‖v - y‖ ^ (2 - (d : ℝ)) :=
    Filter.Eventually.of_forall fun v => Real.rpow_nonneg (norm_nonneg _) _
  have hlhs : ∫ v in E, ‖v - y‖ ^ (2 - (d : ℝ)) =
      (∫⁻ v in E, ENNReal.ofReal (‖v - y‖ ^ (2 - (d : ℝ)))).toReal :=
    integral_eq_lintegral_of_nonneg_ae hnn hint.aestronglyMeasurable
  have hF1 : ∀ᵐ t ∂(volume : Measure ℝ), F t < ⊤ :=
    Filter.Eventually.of_forall fun t =>
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hvolfin t).lt_top
  have hrhs : ∫ t, (F t).toReal = (∫⁻ t, F t).toReal := integral_toReal hFm.aemeasurable hF1
  have hset : ∫ t in Set.Ioi (0 : ℝ), (F t).toReal = ∫ t, (F t).toReal := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
    have : t ≤ 0 := not_lt.mp ht
    simp [hFnonpos t this]
  have hmul : ∫ t in Set.Ioi (0 : ℝ), (F t).toReal =
      ((d : ℝ) - 2) * ∫ t in Set.Ioi (0 : ℝ),
        (volume (E ∩ Metric.ball y t)).toReal * t ^ (1 - (d : ℝ)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    exact hFpos t ht
  rw [hlhs, hL, ← hmul, hset, hrhs]

/-- The layer-cake identity for the part of the range outside the ball of radius `b`: for every
path, time, radius and point, `E = D_n ∖ B(0,b)` is a bounded measurable set and the identity
`layer_cake_eq` holds for it. -/
theorem layer_cake_eq_cellSet (hd : 3 ≤ d) (Y : ℕ → Site d) (n : ℕ) (b : ℝ)
    (y : EuclideanSpace ℝ (Fin d)) :
    ∫ v in cellSet Y n \ Metric.ball 0 b, ‖v - y‖ ^ (2 - (d : ℝ)) =
      ((d : ℝ) - 2) * ∫ t in Set.Ioi (0 : ℝ),
        (volume ((cellSet Y n \ Metric.ball 0 b) ∩ Metric.ball y t)).toReal *
          t ^ (1 - (d : ℝ)) := by
  have hE : MeasurableSet (cellSet Y n \ Metric.ball 0 b) :=
    (CERW.Support.Occupation.measurableSet_cellSet Y n).diff measurableSet_ball
  have hEb : Bornology.IsBounded (cellSet Y n \ Metric.ball 0 b) :=
    (Metric.isBounded_ball.subset
      (CERW.Support.Occupation.cellSet_subset_ball (by omega) Y n)).subset Set.sdiff_subset
  exact (layer_cake_eq hd hE hEb y).2.2

/-! ## The weight, the supremum of the absolute potential and the potential of a ball -/

/-- The radial weight `χ(ζ) = (1 + |ζ|)^{2-2d}` of `ℝ^d` (Step 2 of the proof of
`lem:contact`). -/
noncomputable def chiWeight (d : ℕ) (ζ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ))

/-- The weight `chiWeight` is the weight `ev_chi` of the proofs evaluated at the norm. -/
private lemma chiWeight_eq (ζ : EuclideanSpace ℝ (Fin d)) : chiWeight d ζ = ev_chi d ‖ζ‖ :=
  (ev_chi_norm ζ).symm

/-- The supremum `sup_y |U_E(y)|` of the absolute potential of a set `E`. -/
noncomputable def supAbsPotential (d : ℕ) (ε : ℝ) (E : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  ⨆ z : EuclideanSpace ℝ (Fin d), |potential d ε E z|

/-- The absolute potential of a bounded measurable set is bounded, so the supremum
`supAbsPotential` is the genuine supremum (it is not the junk value of an unbounded supremum). -/
lemma bddAbove_abs_potential (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) :
    BddAbove (Set.range fun z : EuclideanSpace ℝ (Fin d) => |potential d ε E z|) := by
  refine ⟨2 * d * ε * unitBallVolume d ^ (-(1 : ℝ) / d) * (volume E).toReal ^ ((1 : ℝ) / d), ?_⟩
  rintro _ ⟨z, rfl⟩
  exact CERW.Support.Geometry.abs_potential_le hd hε hE hEb.measure_lt_top.ne z

/-- The absolute potential at every point is at most `sup |U_E|`. -/
lemma abs_potential_le_supAbs (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (z : EuclideanSpace ℝ (Fin d)) : |potential d ε E z| ≤ supAbsPotential d ε E :=
  le_ciSup (bddAbove_abs_potential hd hε hE hEb) z

/-- `sup |U_E| ≥ 0`. -/
lemma supAbsPotential_nonneg (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) :
    0 ≤ supAbsPotential d ε E :=
  (abs_nonneg _).trans (abs_potential_le_supAbs hd hε hE hEb 0)

/-- The potential of the ball `B(0,b)` is the cone `2dε (b - |y|)_+`
(`eq:ballpotential-euclid`, for every `b ≥ 0`). -/
lemma potential_ball_eq (hd : 2 ≤ d) (ε : ℝ) {b : ℝ} (hb : 0 ≤ b)
    (y : EuclideanSpace ℝ (Fin d)) :
    potential d ε (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) y =
      2 * d * ε * max (b - ‖y‖) 0 := by
  have h := ev_potential_split hd ε (D := Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)
    measurableSet_ball Metric.isBounded_ball hb subset_rfl y
  rw [Set.sdiff_self] at h
  have h0 : potential d ε (∅ : Set (EuclideanSpace ℝ (Fin d))) y = 0 := by
    simp [potential]
  rw [h0, add_zero] at h
  exact h

/-- The potential is at most `min {U_E^+, sup |U_E|}` at every point. -/
lemma potential_le_min_positive_sup (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (y : EuclideanSpace ℝ (Fin d)) :
    potential d ε E y ≤ min (positivePotential d ε E y) (supAbsPotential d ε E) :=
  le_min (ev_potential_le_positivePotential hd hε hE hEb.measure_lt_top.ne y)
    ((le_abs_self _).trans (abs_potential_le_supAbs hd hε hE hEb y))

/-- **The convolution of the potential with the weight is at most the positive potential**
(Section 6, `d ≥ 3`): `(χ * U_E)(y) ≤ ‖χ‖₁ U_E^+(y)` for every bounded measurable set `E` and every
point `y`. -/
lemma convolution_potential_le_positivePotential (hd : 3 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (y : EuclideanSpace ℝ (Fin d)) :
    ∫ ζ : EuclideanSpace ℝ (Fin d), chiWeight d ζ * potential d ε E (y - ζ) ≤
      (∫ ζ : EuclideanSpace ℝ (Fin d), chiWeight d ζ) * positivePotential d ε E y :=
  newton_conv hd hε hE hEb y

/-- **The absolute convolution of the potential with the weight is at most the supremum**
(Section 6, `d ≥ 3`): `|(χ * U_E)(y)| ≤ ‖χ‖₁ sup |U_E|` for every bounded measurable set `E` and
every point `y`. -/
lemma abs_convolution_potential_le_supAbs (hd : 3 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (y : EuclideanSpace ℝ (Fin d)) :
    |∫ ζ : EuclideanSpace ℝ (Fin d), chiWeight d ζ * potential d ε E (y - ζ)| ≤
      (∫ ζ : EuclideanSpace ℝ (Fin d), chiWeight d ζ) * supAbsPotential d ε E := by
  have hχ : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => chiWeight d ζ) := by
    simpa only [chiWeight_eq] using ev_integrable_chi_norm hd
  have h := norm_integral_le_of_norm_le
    (f := fun ζ : EuclideanSpace ℝ (Fin d) => chiWeight d ζ * potential d ε E (y - ζ))
    (hχ.mul_const (supAbsPotential d ε E)) (Filter.Eventually.of_forall fun ζ => ?_)
  · rw [integral_mul_const] at h
    simpa only [Real.norm_eq_abs] using h
  · have h0 : 0 ≤ chiWeight d ζ := by rw [chiWeight_eq]; exact ev_chi_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (abs_potential_le_supAbs (by omega) hε hE hEb _) h0

/-- The cone `(b - |y - ζ|)_+` is at most `(b - |y|)_+ + min {b, |ζ|}`. -/
private lemma cone_le (b : ℝ) (hb : 0 ≤ b) (y ζ : EuclideanSpace ℝ (Fin d)) :
    max (b - ‖y - ζ‖) 0 ≤ max (b - ‖y‖) 0 + min b ‖ζ‖ := by
  have h1 : ‖y‖ ≤ ‖y - ζ‖ + ‖ζ‖ := by
    calc ‖y‖ = ‖(y - ζ) + ζ‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - ζ‖ + ‖ζ‖ := norm_add_le _ _
  have h2 : 0 ≤ max (b - ‖y‖) 0 := le_max_right _ _
  have h3 : 0 ≤ min b ‖ζ‖ := le_min hb (norm_nonneg ζ)
  have h4 : b - ‖y‖ ≤ max (b - ‖y‖) 0 := le_max_left _ _
  refine max_le ?_ (by linarith)
  rcases le_total ‖ζ‖ b with h | h
  · rw [min_eq_right h]
    linarith [norm_nonneg (y - ζ)]
  · rw [min_eq_left h]
    linarith [norm_nonneg (y - ζ)]

/-! ## `eq:potential-convolution` at every point -/

/-- `eq:potential-convolution` with the explicit radial term, in the weight `ev_chi`: for every
point `y`, `∫ χ(ζ) U_D(y - ζ) dζ ≤ 2dε ∫ χ min{b,|ζ|} + ‖χ‖₁ (2dε (b - |y|)_+ +
min {U_E^+(y), sup |U_E|})`, with `E = D ∖ B(0,b)`. -/
private lemma integral_ev_chi_mul_potential_le (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDb : Bornology.IsBounded D)
    {b : ℝ} (hb : 0 ≤ b) (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ D)
    (y : EuclideanSpace ℝ (Fin d)) :
    ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * potential d ε D (y - ζ) ≤
      2 * d * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖) +
        (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖) *
          (2 * d * ε * max (b - ‖y‖) 0 +
            min (positivePotential d ε (D \ Metric.ball 0 b) y)
              (supAbsPotential d ε (D \ Metric.ball 0 b))) := by
  have hE : MeasurableSet (D \ Metric.ball 0 b) := hD.diff measurableSet_ball
  have hEb : Bornology.IsBounded (D \ Metric.ball 0 b) := hDb.subset Set.sdiff_subset
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hEfin : volume (D \ Metric.ball 0 b) ≠ ⊤ := hEb.measure_lt_top.ne
  have hχ := ev_integrable_chi_norm hd
  have hint0 := ev_integrable_chi_mul_potential hd hε.le hD hDfin y
  have hint2 := ev_integrable_chi_mul_potential hd hε.le hE hEfin y
  have hint1 : Integrable
      (fun ζ : EuclideanSpace ℝ (Fin d) => ev_chi d ‖ζ‖ * min b ‖ζ‖) := by
    refine hχ.mul_bdd (c := b) (continuous_const.min continuous_norm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ζ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hb (norm_nonneg ζ))]
    exact min_le_left _ _
  have hP : 0 ≤ 2 * (d : ℝ) * ε := by positivity
  set a : ℝ := max (b - ‖y‖) 0 with ha
  set m : ℝ := ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ with hm
  have hm0 : 0 ≤ m := integral_nonneg fun ζ => ev_chi_nonneg _
  set P : ℝ := positivePotential d ε (D \ Metric.ball 0 b) y with hPdef
  set M : ℝ := supAbsPotential d ε (D \ Metric.ball 0 b) with hMdef
  have hpt : ∀ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * potential d ε D (y - ζ) ≤
      (2 * d * ε * a) * ev_chi d ‖ζ‖ + (2 * d * ε * (ev_chi d ‖ζ‖ * min b ‖ζ‖) +
        ev_chi d ‖ζ‖ * potential d ε (D \ Metric.ball 0 b) (y - ζ)) := by
    intro ζ
    have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (cone_le b hb y ζ) hP)
      (ev_chi_nonneg (d := d) ‖ζ‖)
    rw [ev_potential_split (by omega) ε hD hDb hb hball (y - ζ)]
    nlinarith [h2]
  have hA : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => (2 * d * ε * a) * ev_chi d ‖ζ‖) :=
    hχ.const_mul _
  have hB1 : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      2 * d * ε * (ev_chi d ‖ζ‖ * min b ‖ζ‖)) := hint1.const_mul _
  have hB : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      2 * d * ε * (ev_chi d ‖ζ‖ * min b ‖ζ‖) +
        ev_chi d ‖ζ‖ * potential d ε (D \ Metric.ball 0 b) (y - ζ)) := hB1.add hint2
  have hNE := newton_conv hd hε.le hE hEb y
  simp only [← ev_chi_norm] at hNE
  have hNEU : ∫ ζ : EuclideanSpace ℝ (Fin d),
      ev_chi d ‖ζ‖ * potential d ε (D \ Metric.ball 0 b) (y - ζ) ≤ m * P := hNE
  have hMU : ∫ ζ : EuclideanSpace ℝ (Fin d),
      ev_chi d ‖ζ‖ * potential d ε (D \ Metric.ball 0 b) (y - ζ) ≤ m * M := by
    calc _ ≤ ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * M := by
          refine integral_mono hint2 (hχ.mul_const M) fun ζ => ?_
          exact mul_le_mul_of_nonneg_left
            ((le_abs_self _).trans (abs_potential_le_supAbs (by omega) hε.le hE hEb (y - ζ)))
            (ev_chi_nonneg _)
      _ = m * M := by rw [integral_mul_const]
  have hmin : ∫ ζ : EuclideanSpace ℝ (Fin d),
      ev_chi d ‖ζ‖ * potential d ε (D \ Metric.ball 0 b) (y - ζ) ≤ m * min P M := by
    rcases le_total P M with h | h
    · rw [min_eq_left h]
      exact hNEU
    · rw [min_eq_right h]
      exact hMU
  calc ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * potential d ε D (y - ζ)
      ≤ ∫ ζ : EuclideanSpace ℝ (Fin d), ((2 * d * ε * a) * ev_chi d ‖ζ‖ +
          (2 * d * ε * (ev_chi d ‖ζ‖ * min b ‖ζ‖) +
            ev_chi d ‖ζ‖ * potential d ε (D \ Metric.ball 0 b) (y - ζ))) :=
        integral_mono hint0 (hA.add hB) hpt
    _ = (2 * d * ε * a) * m + (2 * d * ε * (∫ ζ : EuclideanSpace ℝ (Fin d),
          ev_chi d ‖ζ‖ * min b ‖ζ‖) + ∫ ζ : EuclideanSpace ℝ (Fin d),
            ev_chi d ‖ζ‖ * potential d ε (D \ Metric.ball 0 b) (y - ζ)) := by
        rw [integral_add hA hB, integral_add hB1 hint2, integral_const_mul, integral_const_mul]
    _ ≤ 2 * d * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖) +
          m * (2 * d * ε * a + min P M) := by nlinarith [hmin]

/-- **`eq:potential-convolution`, every point, cone, positive and supremum terms**
(Section 6). Let `d ≥ 3` and `0 < ε`. There is `C` such that for every bounded measurable
set `D` containing the ball `B(0,b)`, every `n ≥ 2` with `0 ≤ b ≤ 2n`, and **every** `y ∈ ℝ^d`,
with `E = D ∖ B(0,b)` and `χ(ζ) = (1 + |ζ|)^{2-2d}`,
`(χ * U_D)(y) ≤ ‖χ‖₁ (U_{B(0,b)}(y) + min {U_E^+(y), sup |U_E|}) + C log n`. -/
theorem potential_convolution (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Set (EuclideanSpace ℝ (Fin d))), MeasurableSet D →
      Bornology.IsBounded D → ∀ (b : ℝ) (n : ℕ), 2 ≤ n → 0 ≤ b → b ≤ 2 * n →
      Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ D → ∀ y : EuclideanSpace ℝ (Fin d),
      ∫ ζ : EuclideanSpace ℝ (Fin d), chiWeight d ζ * potential d ε D (y - ζ) ≤
        (∫ ζ : EuclideanSpace ℝ (Fin d), chiWeight d ζ) *
          (potential d ε (Metric.ball 0 b) y +
            min (positivePotential d ε (D \ Metric.ball 0 b) y)
              (supAbsPotential d ε (D \ Metric.ball 0 b))) + C * Real.log n := by
  have hω := unitBallVolume_pos d
  set CT : ℝ := 1 + Real.log (1 + max 1 (2 * 1)) with hCT
  have hCT0 : 0 ≤ CT := by
    rw [hCT]
    have : 0 ≤ Real.log (1 + max 1 (2 * 1 : ℝ)) :=
      Real.log_nonneg (by linarith [le_max_left (1 : ℝ) (2 * 1)])
    linarith
  refine ⟨2 * d * ε * (d * unitBallVolume d * (CT + 1)) * 2, by positivity, ?_⟩
  intro D hD hDb b n hn hb hbn hball y
  have hL1 : 1 ≤ Real.log ((n : ℝ) + 2) := CERW.Support.Law.one_le_log_add_two hn
  have hL2 := co_log_add_two_le hn
  have hlogn : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hb2 : b ≤ 1 * (2 * n) := by linarith
  have hlog := ev_log_one_add_max_le hn hb2
  have hIB := ev_integral_chi_mul_min_le hd hb
  have hIB' : ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖ ≤
      d * unitBallVolume d * ((CT + 1) * Real.log ((n : ℝ) + 2)) := by
    refine hIB.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    nlinarith
  have hT := integral_ev_chi_mul_potential_le hd hε hD hDb hb hball y
  have hP : 0 ≤ 2 * (d : ℝ) * ε := by positivity
  simp only [chiWeight_eq, potential_ball_eq (by omega) ε hb y]
  have hstep : 2 * (d : ℝ) * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖) ≤
      2 * d * ε * (d * unitBallVolume d * (CT + 1)) * 2 * Real.log n := by
    calc 2 * (d : ℝ) * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖)
        ≤ 2 * d * ε * (d * unitBallVolume d * ((CT + 1) * Real.log ((n : ℝ) + 2))) :=
          mul_le_mul_of_nonneg_left hIB' hP
      _ ≤ 2 * d * ε * (d * unitBallVolume d * ((CT + 1) * (2 * Real.log n))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hL2 (by linarith)) (by positivity)) hP
      _ = 2 * d * ε * (d * unitBallVolume d * (CT + 1)) * 2 * Real.log n := by ring
  linarith


/-! ## `eq:envelopehigh` at every point -/

/-- The bracket `W_y = ∑_x ℓ_n(x) (1 + |x - y|)^{2-2d}` of the local martingale at the site `y`
(`eq:bracket`). -/
noncomputable def bracketSum (d : ℕ) (Y : ℕ → Site d) (n : ℕ) (y : Site d) : ℝ :=
  ∑ x ∈ departureRange Y n, (localTime Y n x : ℝ) * (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ))

/-- The bracket of the source is the bracket sum over the times `j < n` used by the proofs. -/
private lemma bracketSum_eq_braSum (Y : ℕ → Site d) (n : ℕ) (y : Site d) :
    bracketSum d Y n y = braSum Y n y := by
  rw [ev_braSum_eq Y n (Finset.Subset.refl _) y]
  rfl

/-- At a point farther than `2n` from the origin the local time vanishes, for a path with
`|Y_j| ≤ j` and `n ≥ √d / 2`. -/
private lemma cellLocalTime_eq_zero_of_far (Y : ℕ → Site d) (n : ℕ)
    (hY : ∀ j, euclidNorm (Y j) ≤ j) (hsd : Real.sqrt d / 2 ≤ n)
    {y : EuclideanSpace ℝ (Fin d)} (hy : 2 * (n : ℝ) < ‖y‖) : cellLocalTime Y n y = 0 := by
  by_contra hne
  have hpos : 0 < localTime Y n (cellCenter y) := by
    have h : cellLocalTime Y n y = (localTime Y n (cellCenter y) : ℝ) := rfl
    rw [h] at hne
    exact Nat.pos_of_ne_zero (by intro h0; apply hne; simp [h0])
  have hmem : cellCenter y ∈ departureRange Y n := mem_departureRange_iff.mpr hpos
  have hy' : y ∈ cellSet Y n := Set.mem_iUnion₂.mpr ⟨cellCenter y, hmem, mem_cell_cellCenter y⟩
  have h1 := CERW.Support.Occupation.norm_le_of_mem_cellSet Y n hy'
  have h2 := ev_maxRadius_le_nat Y n hY
  linarith

/-- A ball inside the open ball of radius `R ≥ 0` has radius at most `R`. -/
private lemma le_of_ball_subset_ball (hd : 1 ≤ d) {b R : ℝ} (hR : 0 ≤ R)
    (h : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ Metric.ball 0 R) : b ≤ R := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  by_contra hlt
  push Not at hlt
  obtain ⟨v, hv⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin d))
    (show 0 ≤ (R + b) / 2 by linarith)
  have hvb : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b := by
    rw [mem_ball_zero_iff, hv]; linarith
  have := mem_ball_zero_iff.mp (h hvb)
  rw [hv] at this
  linarith

/-- The potential step at every point: the `a`-weighted sum of the potential over the lattice ball
of radius `2n` is at most `β L + m (U_{B(0,b)}(y₀) + min {U_E^+(y₀), sup |U_E|})`, where
`m = ∫ χ`, `E = D_n ∖ B(0,b)`, `L = log (n + 2)`, for every `y₀` with `|y₀| ≤ 2n`. -/
private lemma sum_cellWeight_mul_potential_le_full (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {C₃ : ℝ} (hC₃ : 0 ≤ C₃) :
    ∃ β : ℝ, 0 ≤ β ∧ ∀ (X : ℕ → Site d) (n : ℕ), 2 ≤ n → 4 * Real.sqrt d ≤ n →
      (∀ j, euclidNorm (X j) ≤ j) →
      (∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * ((n : ℝ) + Real.sqrt d) →
        ‖y - z‖ ≤ Real.sqrt d →
        |potential d ε (cellSet X n) y - potential d ε (cellSet X n) z| ≤
          C₃ * Real.log ((n : ℝ) + 2)) →
      ∀ (b : ℝ) (y₀ : EuclideanSpace ℝ (Fin d)), 0 ≤ b → b ≤ 2 * n →
        Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ cellSet X n → ‖y₀‖ ≤ 2 * n →
        ∑ y ∈ LatticeProb.ballFinset d (2 * n),
            ev_cellWeight d y₀ y * potential d ε (cellSet X n) (toSpace y) ≤
          β * Real.log ((n : ℝ) + 2) +
            (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖) *
              (2 * d * ε * max (b - ‖y₀‖) 0 +
                min (positivePotential d ε (cellSet X n \ Metric.ball 0 b) y₀)
                  (supAbsPotential d ε (cellSet X n \ Metric.ball 0 b))) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have hω := unitBallVolume_pos d
  set m : ℝ := ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ with hm
  have hm0 : 0 ≤ m := integral_nonneg fun ζ => ev_chi_nonneg _
  set Cf : ℝ := 2 * ε / unitBallVolume d * 2 with hCf
  have hCf0 : 0 ≤ Cf := by rw [hCf]; positivity
  set CT : ℝ := 1 + Real.log (1 + max 1 (2 * 1)) with hCT
  have hCT0 : 0 ≤ CT := by
    rw [hCT]
    have : 0 ≤ Real.log (1 + max 1 (2 * 1 : ℝ)) :=
      Real.log_nonneg (by linarith [le_max_left (1 : ℝ) (2 * 1)])
    linarith
  refine ⟨2 * d * ε * (d * unitBallVolume d * (CT + 1)) + (C₃ + Cf) * m, by positivity, ?_⟩
  intro X n hn hn4 hXn hmod b y₀ hb hbn hball hyn
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hL1 : 1 ≤ L := CERW.Support.Law.one_le_log_add_two hn
  have hsd0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hDmeas : MeasurableSet (cellSet X n) := CERW.Support.Occupation.measurableSet_cellSet X n
  have hDbdd : Bornology.IsBounded (cellSet X n) :=
    (Metric.isBounded_ball (x := (0 : EuclideanSpace ℝ (Fin d)))
      (r := maxRadius X n + Real.sqrt d)).subset
      (CERW.Support.Occupation.cellSet_subset_ball hd1 X n)
  have hDfin : volume (cellSet X n) ≠ ⊤ := hDbdd.measure_lt_top.ne
  set G : EuclideanSpace ℝ (Fin d) → ℝ := fun ζ => ev_chi d ‖y₀ - ζ‖ with hG
  set Uf : EuclideanSpace ℝ (Fin d) → ℝ := fun ζ => potential d ε (cellSet X n) ζ with hUf
  have hG0 : ∀ ζ, 0 ≤ G ζ := fun ζ => ev_chi_nonneg _
  have hGint : Integrable G := (ev_integrable_chi_norm hd).comp_sub_left y₀
  have hGU : Integrable (fun ζ => G ζ * Uf ζ) := by
    have := (ev_integrable_chi_mul_potential hd hε.le hDmeas hDfin y₀).comp_sub_left y₀
    simpa only [sub_sub_cancel] using this
  have hGUint : ∫ ζ, G ζ * Uf ζ =
      ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * potential d ε (cellSet X n) (y₀ - ζ) := by
    have := integral_sub_left_eq_self
      (fun ζ : EuclideanSpace ℝ (Fin d) =>
        ev_chi d ‖ζ‖ * potential d ε (cellSet X n) (y₀ - ζ)) volume y₀
    simpa only [sub_sub_cancel] using this
  have hGm : ∫ ζ, G ζ = m :=
    integral_sub_left_eq_self (fun ζ : EuclideanSpace ℝ (Fin d) => ev_chi d ‖ζ‖) volume y₀
  have hmod' : ∀ y ∈ LatticeProb.ballFinset d (2 * n), ∀ ζ ∈ cell y,
      Uf (toSpace y) ≤ Uf ζ + C₃ * L := by
    intro y hy ζ hζ
    rw [LatticeProb.mem_ballFinset_iff] at hy
    have h1 := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hζ
    have h2 := hmod (toSpace y) ζ (by rw [norm_toSpace]; linarith) (by
      rw [norm_sub_rev]; linarith)
    have := (abs_le.mp h2).2
    simp only [hUf]
    linarith
  have hfar : ∀ ζ ∉ ⋃ y ∈ LatticeProb.ballFinset d (2 * n), cell y, -Cf ≤ Uf ζ := fun ζ hζ =>
    ev_neg_le_potential_of_not_mem hd2 hε.le hn hn4 hXn hζ
  have hsum := ev_sum_setIntegral_mul_le (S := LatticeProb.ballFinset d (2 * n)) (M := C₃ * L)
    (Cf := Cf) hG0 hGint hGU (mul_nonneg hC₃ (by linarith)) hCf0 hmod' hfar
  have hb2 : b ≤ 1 * (2 * n) := by linarith
  have hlog := ev_log_one_add_max_le hn hb2
  have hIB := ev_integral_chi_mul_min_le hd hb
  have hIB' : ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖ ≤
      d * unitBallVolume d * ((CT + 1) * L) := by
    refine hIB.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    linarith
  have hconv := integral_ev_chi_mul_potential_le hd hε hDmeas hDbdd hb hball y₀
  have hP : 0 ≤ 2 * (d : ℝ) * ε := by positivity
  set Q : ℝ := 2 * d * ε * max (b - ‖y₀‖) 0 +
    min (positivePotential d ε (cellSet X n \ Metric.ball 0 b) y₀)
      (supAbsPotential d ε (cellSet X n \ Metric.ball 0 b)) with hQ
  have hstep : 2 * (d : ℝ) * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖) ≤
      2 * d * ε * (d * unitBallVolume d * (CT + 1)) * L := by
    calc 2 * (d : ℝ) * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖)
        ≤ 2 * d * ε * (d * unitBallVolume d * ((CT + 1) * L)) :=
          mul_le_mul_of_nonneg_left hIB' hP
      _ = 2 * d * ε * (d * unitBallVolume d * (CT + 1)) * L := by ring
  have hCfm : Cf * m ≤ Cf * m * L := by
    have := mul_nonneg (mul_nonneg hCf0 hm0) (sub_nonneg.mpr hL1)
    linarith
  calc ∑ y ∈ LatticeProb.ballFinset d (2 * n),
          ev_cellWeight d y₀ y * potential d ε (cellSet X n) (toSpace y)
      ≤ (∫ ζ, G ζ * Uf ζ) + (C₃ * L + Cf) * ∫ ζ, G ζ := hsum
    _ ≤ (2 * d * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖) + m * Q) +
          (C₃ * L + Cf) * m := by
        rw [hGm, hGUint]
        linarith
    _ ≤ (2 * d * ε * (d * unitBallVolume d * (CT + 1)) + (C₃ + Cf) * m) * L + m * Q := by
        linarith

/-- **The envelope with the potential of the ball, the positive potential and the supremum of the
absolute potential** (deterministic core of `eq:envelopehigh`). Let `d ≥ 3`, `0 < ε`. There are
`C` and `n₀` such that, for every path from the origin with unit steps that satisfies the
pointwise approximation of the local time by the potential with its bracket (`eq:pointwise`,
`eq:localmart`) at the lattice points `|x| ≤ 3n`, every `n ≥ n₀`, every `b ≥ 0` with
`B(0,b) ⊂ D_n` and every `y` with `|y| ≤ 2n`, the bracket at the cell centre of `y` and the local
time there are at most `C (log (n + 2) + 2dε (b - |y|)_+ + min {U_E^+(y), sup |U_E|})`,
`E = D_n ∖ B(0,b)`. -/
private theorem envelope_core (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) (c₁ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      (∀ j, euclidNorm (Y j) ≤ j) →
      (∀ x : Site d, euclidNorm x ≤ 3 * n →
        |(localTime Y n x : ℝ) - potential d ε (cellSet Y n) (toSpace x)| ≤
          c₁ * (Real.sqrt (braSum Y n x * Real.log ((n : ℝ) + 2)) + Real.log ((n : ℝ) + 2))) →
      ∀ b : ℝ, 0 ≤ b → Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ cellSet Y n →
      ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
        braSum Y n (cellCenter y) ≤ C * (Real.log ((n : ℝ) + 2) +
          (2 * d * ε * max (b - ‖y‖) 0 +
            min (positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y)
              (supAbsPotential d ε (cellSet Y n \ Metric.ball 0 b)))) ∧
        (localTime Y n (cellCenter y) : ℝ) ≤ C * (Real.log ((n : ℝ) + 2) +
          (2 * d * ε * max (b - ‖y‖) 0 +
            min (positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y)
              (supAbsPotential d ε (cellSet Y n \ Metric.ball 0 b)))) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  set C₁ : ℝ := max c₁ 0 with hC₁def
  have hC₁ : 0 ≤ C₁ := le_max_right _ _
  obtain ⟨CM, hCM0, hCM⟩ := CERW.Support.Geometry.exists_potential_cell_modulus hd2
  set C₃ : ℝ := 2 * CM * ε with hC₃def
  have hC₃ : 0 ≤ C₃ := by positivity
  obtain ⟨c₀, α₁, hc₀, hα₁, hlat⟩ := ev_kernel_sum_le hd hC₁
  obtain ⟨β, hβ, hpot⟩ := sum_cellWeight_mul_potential_le_full hd hε hC₃
  set m : ℝ := ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ with hm
  have hm0 : 0 ≤ m := integral_nonneg fun ζ => ev_chi_nonneg _
  set K : ℝ := (2 * β + α₁ + 2 * m) / c₀ with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨1 + C₃ + C₁ * K + 2 * C₁ + K, by positivity, max 2 ⌈4 * Real.sqrt d⌉₊, ?_⟩
  intro Y n hn hYn hfine b hb hball y hyn
  have hn2 : 2 ≤ n := le_of_max_le_left hn
  have hn4 : 4 * Real.sqrt d ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hn)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hsd0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hL1 : 1 ≤ L := CERW.Support.Law.one_le_log_add_two hn2
  have hmax : maxRadius Y n ≤ n := ev_maxRadius_le_nat Y n hYn
  have hDmeas : MeasurableSet (cellSet Y n) := CERW.Support.Occupation.measurableSet_cellSet Y n
  have hDsub : cellSet Y n ⊆ Metric.ball 0 ((n : ℝ) + Real.sqrt d) :=
    (CERW.Support.Occupation.cellSet_subset_ball hd1 Y n).trans
      (Metric.ball_subset_ball (by linarith))
  have hDbdd : Bornology.IsBounded (cellSet Y n) := Metric.isBounded_ball.subset hDsub
  have hEmeas : MeasurableSet (cellSet Y n \ Metric.ball 0 b) := hDmeas.diff measurableSet_ball
  have hEb : Bornology.IsBounded (cellSet Y n \ Metric.ball 0 b) :=
    hDbdd.subset Set.sdiff_subset
  have hEfin : volume (cellSet Y n \ Metric.ball 0 b) ≠ ⊤ := hEb.measure_lt_top.ne
  have hbn : b ≤ 2 * n := by
    have := le_of_ball_subset_ball hd1 (by linarith) (hball.trans hDsub)
    linarith
  have hfine₁ : ∀ x : Site d, euclidNorm x ≤ 3 * n →
      |(localTime Y n x : ℝ) - potential d ε (cellSet Y n) (toSpace x)| ≤
        C₁ * (Real.sqrt (braSum Y n x * L) + L) := by
    intro x hx
    exact (hfine x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (add_nonneg (Real.sqrt_nonneg _) (by linarith)))
  have hmod : ∀ u v : EuclideanSpace ℝ (Fin d), ‖u‖ ≤ 2 * ((n : ℝ) + Real.sqrt d) →
      ‖u - v‖ ≤ Real.sqrt d →
      |potential d ε (cellSet Y n) u - potential d ε (cellSet Y n) v| ≤ C₃ * L := by
    intro u v hu huv
    have h := hCM ε hε.le ((n : ℝ) + Real.sqrt d) (by linarith) (cellSet Y n) hDmeas hDsub
      u v hu huv
    have hsq : (n : ℝ) + Real.sqrt d + 2 ≤ ((n : ℝ) + 2) ^ 2 := by
      have e : ((n : ℝ) + 2) ^ 2 = (n : ℝ) * n + 3 * n + 2 + ((n : ℝ) + 2) := by ring
      have := mul_nonneg hn0 hn0
      linarith
    have hlog : Real.log ((n : ℝ) + Real.sqrt d + 2) ≤ 2 * L := by
      have h3 : Real.log (((n : ℝ) + 2) ^ 2) = 2 * L := by
        rw [Real.log_pow, hL]
        norm_num
      rw [← h3]
      exact Real.log_le_log (by linarith) hsq
    calc |potential d ε (cellSet Y n) u - potential d ε (cellSet Y n) v|
        ≤ CM * ε * Real.log ((n : ℝ) + Real.sqrt d + 2) := h
      _ ≤ CM * ε * (2 * L) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = C₃ * L := by rw [hC₃def]; ring
  have hzy : ‖toSpace (cellCenter y) - y‖ ≤ Real.sqrt d / 2 := by
    rw [norm_sub_rev]
    exact CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell (mem_cell_cellCenter y)
  set P : ℝ := positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y with hPdef
  set M : ℝ := supAbsPotential d ε (cellSet Y n \ Metric.ball 0 b) with hMdef
  have hP0 : 0 ≤ P := ev_positivePotential_nonneg hε.le _ _
  have hM0 : 0 ≤ M := supAbsPotential_nonneg hd1 hε.le hEmeas hEb
  set Q : ℝ := 2 * d * ε * max (b - ‖y‖) 0 + min P M with hQdef
  have hQ0 : 0 ≤ Q := by
    have h1 : 0 ≤ 2 * (d : ℝ) * ε * max (b - ‖y‖) 0 :=
      mul_nonneg (by positivity) (le_max_right _ _)
    have h2 : 0 ≤ min P M := le_min hP0 hM0
    rw [hQdef]
    linarith
  set W : ℝ := braSum Y n (cellCenter y) with hWdef
  have hb1 : c₀ * W ≤ 2 * ∑ x ∈ LatticeProb.ballFinset d (2 * n),
      ev_cellWeight d y x * potential d ε (cellSet Y n) (toSpace x) + α₁ * L :=
    hlat Y n (fun x => potential d ε (cellSet Y n) (toSpace x)) hYn hfine₁ y (cellCenter y) hzy
  have hb2 : ∑ x ∈ LatticeProb.ballFinset d (2 * n),
      ev_cellWeight d y x * potential d ε (cellSet Y n) (toSpace x) ≤ β * L + m * Q :=
    hpot Y n hn2 hn4 hYn hmod b y hb hbn hball hyn
  have hW0 : 0 ≤ W := by
    rw [hWdef]
    unfold braSum
    exact Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (by linarith [LatticeProb.euclidNorm_nonneg (Y j - cellCenter y)]) _
  have hW : W ≤ K * (L + Q) := by
    refine le_of_mul_le_mul_left ?_ hc₀
    have h1 : c₀ * W ≤ (2 * β + α₁) * L + 2 * m * Q := by
      linarith
    have h2 : c₀ * (K * (L + Q)) = (2 * β + α₁ + 2 * m) * (L + Q) := by
      rw [hK]
      field_simp
    rw [h2]
    have h3 : 0 ≤ (2 * β + α₁) * Q := mul_nonneg (by linarith) hQ0
    have h4 : 0 ≤ 2 * m * L := mul_nonneg (by linarith) (by linarith)
    linarith
  have hLQ : 0 ≤ L + Q := by linarith
  have hKC : K ≤ 1 + C₃ + C₁ * K + 2 * C₁ + K := by
    have := mul_nonneg hC₁ hK0
    linarith
  refine ⟨hW.trans (mul_le_mul_of_nonneg_right hKC hLQ), ?_⟩
  have hzn : euclidNorm (cellCenter y) ≤ 3 * n := by
    have h1 : ‖toSpace (cellCenter y)‖ - ‖y‖ ≤ ‖toSpace (cellCenter y) - y‖ :=
      norm_sub_norm_le _ _
    rw [norm_toSpace] at h1
    linarith
  have hℓ : (localTime Y n (cellCenter y) : ℝ) -
      potential d ε (cellSet Y n) (toSpace (cellCenter y)) ≤ C₁ * (Real.sqrt (W * L) + L) :=
    (abs_le.mp (hfine₁ (cellCenter y) hzn)).2
  have hUz : potential d ε (cellSet Y n) (toSpace (cellCenter y)) ≤
      potential d ε (cellSet Y n) y + C₃ * L := by
    have h := hmod y (toSpace (cellCenter y)) (by linarith)
      (by rw [norm_sub_rev]; linarith)
    have := (abs_le.mp h).1
    linarith
  have hUy : potential d ε (cellSet Y n) y ≤ Q := by
    have hsplit := ev_potential_split hd2 ε hDmeas hDbdd hb hball y
    have hUE1 : potential d ε (cellSet Y n \ Metric.ball 0 b) y ≤ P :=
      ev_potential_le_positivePotential hd1 hε.le hEmeas hEfin y
    have hUE2 : potential d ε (cellSet Y n \ Metric.ball 0 b) y ≤ M :=
      (le_abs_self _).trans (abs_potential_le_supAbs hd1 hε.le hEmeas hEb y)
    have hmin := le_min hUE1 hUE2
    rw [hsplit, hQdef]
    linarith
  have hsqrt : Real.sqrt (W * L) ≤ W + L := by
    have h1 : W * L ≤ (W + L) ^ 2 := by
      have e : (W + L) ^ 2 = W * L + (W * W + W * L + L * L) := by ring
      have := mul_nonneg hW0 hW0
      have := mul_nonneg hW0 (by linarith : (0 : ℝ) ≤ L)
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ L) (by linarith : (0 : ℝ) ≤ L)
      linarith
    calc Real.sqrt (W * L) ≤ Real.sqrt ((W + L) ^ 2) := Real.sqrt_le_sqrt h1
      _ = W + L := Real.sqrt_sq (by linarith)
  have hC₁sq : C₁ * Real.sqrt (W * L) ≤ C₁ * (K * (L + Q) + L) :=
    mul_le_mul_of_nonneg_left (hsqrt.trans (by linarith)) hC₁
  have e : (1 + C₃ + C₁ * K + 2 * C₁ + K) * (L + Q) =
      (Q + C₃ * L + C₁ * (K * (L + Q) + L) + C₁ * L) +
        (L + C₃ * Q + 2 * C₁ * Q + K * (L + Q)) := by ring
  have h5 : 0 ≤ C₃ * Q := mul_nonneg hC₃ hQ0
  have h6 : 0 ≤ 2 * C₁ * Q := mul_nonneg (by linarith) hQ0
  have h7 : 0 ≤ K * (L + Q) := mul_nonneg hK0 hLQ
  have h8 : (localTime Y n (cellCenter y) : ℝ) ≤
      Q + C₃ * L + C₁ * (K * (L + Q) + L) + C₁ * L := by
    have e2 : C₁ * (Real.sqrt (W * L) + L) = C₁ * Real.sqrt (W * L) + C₁ * L := by ring
    linarith
  linarith


/-- **`eq:potential-convolution` for the range of a path, with no bound on `b` assumed.** Let
`d ≥ 3` and `0 < ε`. There are `C` and `n₀` such that for every path with `|Y_j| ≤ j`, every
`n ≥ n₀`, every `b ≥ 0` with `B(0,b) ⊂ D_n` and every `y ∈ ℝ^d`, with `E = D_n ∖ B(0,b)`,
`(χ * U_{D_n})(y) ≤ ‖χ‖₁ (U_{B(0,b)}(y) + min {U_E^+(y), sup |U_E|}) + C log n`. The bound
`b ≤ 2n` needed by `potential_convolution` follows from the inclusion `B(0,b) ⊂ D_n`. -/
theorem potential_convolution_cellSet (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      (∀ j, euclidNorm (Y j) ≤ j) →
      ∀ b : ℝ, 0 ≤ b → Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ cellSet Y n →
      ∀ y : EuclideanSpace ℝ (Fin d),
      ∫ ζ : EuclideanSpace ℝ (Fin d), chiWeight d ζ * potential d ε (cellSet Y n) (y - ζ) ≤
        (∫ ζ : EuclideanSpace ℝ (Fin d), chiWeight d ζ) *
          (potential d ε (Metric.ball 0 b) y +
            min (positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y)
              (supAbsPotential d ε (cellSet Y n \ Metric.ball 0 b))) + C * Real.log n := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C, hC, hpc⟩ := potential_convolution hd hε
  refine ⟨C, hC, max 2 ⌈Real.sqrt d⌉₊, ?_⟩
  intro Y n hn hYn b hb hball y
  have hn2 : 2 ≤ n := le_of_max_le_left hn
  have hsdn : Real.sqrt d ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hn)
  have hDsub : cellSet Y n ⊆ Metric.ball 0 (maxRadius Y n + Real.sqrt d) :=
    CERW.Support.Occupation.cellSet_subset_ball hd1 Y n
  have hmax : maxRadius Y n ≤ n := ev_maxRadius_le_nat Y n hYn
  have hbn : b ≤ 2 * n := by
    have := le_of_ball_subset_ball hd1
      (by linarith [Real.sqrt_nonneg (d : ℝ), gd_maxRadius_nonneg Y n]) (hball.trans hDsub)
    linarith
  exact hpc _ (CERW.Support.Occupation.measurableSet_cellSet Y n)
    (Metric.isBounded_ball.subset hDsub) b n hn2 hb hbn hball y

/-- **`eq:envelopehigh` at every point** (Section 6). Let `d ≥ 3`, `0 < ε`, `c₁` a constant.
There are `C` and `n₀` such that for every path from the origin with unit steps that satisfies
the approximation of the local time by the potential with its bracket, `|ℓ_n(x) - U_{D_n}(x)| ≤
c₁ (√(W_x log (n + 2)) + log (n + 2))` for `|x| ≤ 3n` (`eq:pointwise`, `eq:localmart`), every
`n ≥ n₀`, every `b ≥ 0` with `B(0,b) ⊂ D_n`, and **every** `y ∈ ℝ^d`, with `E = D_n ∖ B(0,b)`:
`ℓ~_n(y) ≤ C ((b - |y|)_+ + sup |U_E| + log n)`, and, if `|y| ≥ b`,
`ℓ~_n(y) ≤ C (U_E^+(y) + log n)`. -/
theorem envelope_high_full (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) (c₁ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      (∀ j, euclidNorm (Y j) ≤ j) →
      (∀ x : Site d, euclidNorm x ≤ 3 * n →
        |(localTime Y n x : ℝ) - potential d ε (cellSet Y n) (toSpace x)| ≤
          c₁ * (Real.sqrt (bracketSum d Y n x * Real.log ((n : ℝ) + 2)) +
            Real.log ((n : ℝ) + 2))) →
      ∀ b : ℝ, 0 ≤ b → Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ cellSet Y n →
      ∀ y : EuclideanSpace ℝ (Fin d),
        cellLocalTime Y n y ≤ C * (max (b - ‖y‖) 0 +
          supAbsPotential d ε (cellSet Y n \ Metric.ball 0 b) + Real.log n) ∧
        (b ≤ ‖y‖ → cellLocalTime Y n y ≤
          C * (positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y + Real.log n)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C, hC, n₀, h⟩ := envelope_core hd hε c₁
  refine ⟨C * (2 + 2 * d * ε), by positivity, max n₀ (max 2 ⌈4 * Real.sqrt d⌉₊), ?_⟩
  intro Y n hn hYn hfine b hb hball y
  have hn₀ : n₀ ≤ n := le_of_max_le_left hn
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) (le_of_max_le_right hn)
  have hn4 : 4 * Real.sqrt d ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast
      (le_max_right _ _).trans (le_of_max_le_right hn))
  have hsd0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hfine' : ∀ x : Site d, euclidNorm x ≤ 3 * n →
      |(localTime Y n x : ℝ) - potential d ε (cellSet Y n) (toSpace x)| ≤
        c₁ * (Real.sqrt (braSum Y n x * Real.log ((n : ℝ) + 2)) +
          Real.log ((n : ℝ) + 2)) := by
    intro x hx
    simpa only [bracketSum_eq_braSum] using hfine x hx
  have hEmeas : MeasurableSet (cellSet Y n \ Metric.ball 0 b) :=
    (CERW.Support.Occupation.measurableSet_cellSet Y n).diff measurableSet_ball
  have hEb : Bornology.IsBounded (cellSet Y n \ Metric.ball 0 b) :=
    (Metric.isBounded_ball.subset
      (CERW.Support.Occupation.cellSet_subset_ball hd1 Y n)).subset Set.sdiff_subset
  have hP0 : 0 ≤ positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y :=
    ev_positivePotential_nonneg hε.le _ _
  have hM0 : 0 ≤ supAbsPotential d ε (cellSet Y n \ Metric.ball 0 b) :=
    supAbsPotential_nonneg hd1 hε.le hEmeas hEb
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hL2 := co_log_add_two_le hn2
  have hL1 : 1 ≤ Real.log ((n : ℝ) + 2) := CERW.Support.Law.one_le_log_add_two hn2
  have hcl : cellLocalTime Y n y = (localTime Y n (cellCenter y) : ℝ) := rfl
  have hP : 0 ≤ 2 * (d : ℝ) * ε := by positivity
  have ha0 : 0 ≤ max (b - ‖y‖) 0 := le_max_right _ _
  have hmin0 : 0 ≤ min (positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y)
      (supAbsPotential d ε (cellSet Y n \ Metric.ball 0 b)) := le_min hP0 hM0
  have hkey : cellLocalTime Y n y ≤ C * (Real.log ((n : ℝ) + 2) +
      (2 * d * ε * max (b - ‖y‖) 0 +
        min (positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y)
          (supAbsPotential d ε (cellSet Y n \ Metric.ball 0 b)))) := by
    by_cases hy : ‖y‖ ≤ 2 * n
    · rw [hcl]
      exact (h Y n hn₀ hYn hfine' b hb hball y hy).2
    · rw [cellLocalTime_eq_zero_of_far Y n hYn (by linarith) (not_le.mp hy)]
      have : 0 ≤ 2 * (d : ℝ) * ε * max (b - ‖y‖) 0 := mul_nonneg hP ha0
      positivity
  have hK : 0 ≤ C := hC.le
  constructor
  · refine hkey.trans ?_
    have hmin : min (positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y)
        (supAbsPotential d ε (cellSet Y n \ Metric.ball 0 b)) ≤
        supAbsPotential d ε (cellSet Y n \ Metric.ball 0 b) := min_le_right _ _
    have h1 : Real.log ((n : ℝ) + 2) + (2 * d * ε * max (b - ‖y‖) 0 +
        min (positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y)
          (supAbsPotential d ε (cellSet Y n \ Metric.ball 0 b))) ≤
        (2 + 2 * d * ε) * (max (b - ‖y‖) 0 +
          supAbsPotential d ε (cellSet Y n \ Metric.ball 0 b) + Real.log n) := by
      nlinarith [mul_nonneg hP hM0, mul_nonneg hP hlogn, mul_nonneg hP ha0]
    calc C * _ ≤ C * ((2 + 2 * d * ε) * (max (b - ‖y‖) 0 +
          supAbsPotential d ε (cellSet Y n \ Metric.ball 0 b) + Real.log n)) :=
          mul_le_mul_of_nonneg_left h1 hK
      _ = C * (2 + 2 * d * ε) * (max (b - ‖y‖) 0 +
          supAbsPotential d ε (cellSet Y n \ Metric.ball 0 b) + Real.log n) := by ring
  · intro hby
    refine hkey.trans ?_
    have hzero : max (b - ‖y‖) 0 = 0 := max_eq_right (by linarith)
    have hmin : min (positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y)
        (supAbsPotential d ε (cellSet Y n \ Metric.ball 0 b)) ≤
        positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y := min_le_left _ _
    have h1 : Real.log ((n : ℝ) + 2) + (2 * d * ε * max (b - ‖y‖) 0 +
        min (positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y)
          (supAbsPotential d ε (cellSet Y n \ Metric.ball 0 b))) ≤
        (2 + 2 * d * ε) * (positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y +
          Real.log n) := by
      rw [hzero]
      nlinarith [mul_nonneg hP hP0, mul_nonneg hP hlogn]
    calc C * _ ≤ C * ((2 + 2 * d * ε) * (positivePotential d ε
          (cellSet Y n \ Metric.ball 0 b) y + Real.log n)) :=
          mul_le_mul_of_nonneg_left h1 hK
      _ = C * (2 + 2 * d * ε) * (positivePotential d ε
          (cellSet Y n \ Metric.ball 0 b) y + Real.log n) := by ring

/-- The displays `eq:potential-convolution` and `eq:envelopehigh` for the actual set `D_n`, the
inner radius `b = R_in(n)` and the constants `Cc`, `Ce`, at every point `y ∈ ℝ^d`. -/
def EnvelopeHighDisplays (d : ℕ) (ε Cc Ce : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop :=
  ∀ y : EuclideanSpace ℝ (Fin d),
    ∫ ζ : EuclideanSpace ℝ (Fin d), chiWeight d ζ * potential d ε (cellSet Y n) (y - ζ) ≤
        (∫ ζ : EuclideanSpace ℝ (Fin d), chiWeight d ζ) *
          (potential d ε (Metric.ball 0 (innerRadius Y n)) y +
            min (positivePotential d ε (cellSet Y n \ Metric.ball 0 (innerRadius Y n)) y)
              (supAbsPotential d ε (cellSet Y n \ Metric.ball 0 (innerRadius Y n)))) +
          Cc * Real.log n ∧
      cellLocalTime Y n y ≤ Ce * (max (innerRadius Y n - ‖y‖) 0 +
        supAbsPotential d ε (cellSet Y n \ Metric.ball 0 (innerRadius Y n)) + Real.log n) ∧
      (innerRadius Y n ≤ ‖y‖ → cellLocalTime Y n y ≤
        Ce * (positivePotential d ε (cellSet Y n \ Metric.ball 0 (innerRadius Y n)) y +
          Real.log n))

/-- **The displays at the inner radius, with high probability.** For `d ≥ 3`, `0 < ε < 1/d` and
`p > 0` there are constants `Cc`, `Ce`, `Cp`, chosen before the probability space, the walk and
`n`, such that for every centrally excited random walk and every `n ≥ 2`, with probability at
least `1 - Cp n^{-p}` the displays `eq:potential-convolution` and `eq:envelopehigh` hold at every
point `y` for `b = R_in(n)`. -/
theorem envelope_high_prob (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    {p : ℝ} (hp : 0 < p) :
    ∃ Cc Ce Cp : ℝ, 0 < Cc ∧ 0 < Ce ∧ 0 < Cp ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ EnvelopeHighDisplays d ε Cc Ce (fun j => X j ω) n} ≤
          ENNReal.ofReal (Cp * (n : ℝ) ^ (-p)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₀, C₁, Cf, hC₀, hC₁, hCf, hfl⟩ := exists_pathFacts_prob (by omega : 2 ≤ d) hε hεd hp
  obtain ⟨Ce, hCe, n₀, henv⟩ := envelope_high_full hd hε C₁
  obtain ⟨Cc, hCc, hpc⟩ := potential_convolution hd hε
  set N : ℕ := max n₀ ⌈Real.sqrt d⌉₊ with hN
  have hNp : 0 < ((N : ℝ) + 1) ^ p := Real.rpow_pos_of_pos (by positivity) p
  refine ⟨Cc, Ce, Cf + ((N : ℝ) + 1) ^ p, hCc, hCe, by positivity, ?_⟩
  intro Ω _ μ _ X hX n hn2
  by_cases hnb : N ≤ n
  · have hnn₀ : n₀ ≤ n := le_of_max_le_left hnb
    have hsdn : Real.sqrt d ≤ n :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hnb)
    have key : ∀ Y : ℕ → Site d, PathFacts d ε C₀ C₁ Y n → EnvelopeHighDisplays d ε Cc Ce Y n := by
      intro Y hPF y
      obtain ⟨hstart, hstep, -, -, -, hpoint, -⟩ := hPF
      have hYn : ∀ j, euclidNorm (Y j) ≤ j :=
        CERW.Support.Occupation.euclidNorm_le_of_steps Y hstart hstep
      have hmax : maxRadius Y n ≤ n := ev_maxRadius_le_nat Y n hYn
      have hball := ball_innerRadius_subset hd1 Y n
      have hb0 : 0 ≤ innerRadius Y n := innerRadius_nonneg Y n
      have hDsub : cellSet Y n ⊆ Metric.ball 0 (maxRadius Y n + Real.sqrt d) :=
        CERW.Support.Occupation.cellSet_subset_ball hd1 Y n
      have hDmeas := CERW.Support.Occupation.measurableSet_cellSet Y n
      have hDb : Bornology.IsBounded (cellSet Y n) := Metric.isBounded_ball.subset hDsub
      have hfine : ∀ x : Site d, euclidNorm x ≤ 3 * n →
          |(localTime Y n x : ℝ) - potential d ε (cellSet Y n) (toSpace x)| ≤
            C₁ * (Real.sqrt (bracketSum d Y n x * Real.log ((n : ℝ) + 2)) +
              Real.log ((n : ℝ) + 2)) := by
        intro x hx
        rw [bracketSum_eq_braSum]
        exact hpoint x hx
      have hbn : innerRadius Y n ≤ 2 * n := by
        have := le_of_ball_subset_ball hd1
          (by linarith [Real.sqrt_nonneg (d : ℝ), gd_maxRadius_nonneg Y n]) (hball.trans hDsub)
        linarith
      exact ⟨hpc _ hDmeas hDb (innerRadius Y n) n hn2 hb0 hbn hball y,
        henv Y n hnn₀ hYn hfine _ hb0 hball y⟩
    refine le_trans (measure_mono ?_) ((hfl μ X hX n hn2).trans
      (ENNReal.ofReal_le_ofReal ?_))
    · intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      intro hPF
      exact hω (key _ hPF)
    · have : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      nlinarith
  · exact (prob_le_one).trans (one_le_ofReal_mul_rpow hp (by omega) (not_le.mp hnb)
      (by linarith))


/-! ## The planar displays -/

open private radius qrate tk_qrate_le_one tk_rq_rpow radius_pos qrate_nonneg innerRadius_le
  sdiff_subset_annulus annulus_potential_le tk_radius_eq hx_scales hx_log_facts co_qrate_pos
  from CERW.Support.Outer.OuterRadius

/-- The radius `r_n = ((d + 1) n / (2 d ε ω_d))^{1/(d+1)}` of `eq:radius`. -/
noncomputable def sourceRadius (d : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  ((d + 1) * n / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1))

/-- The rate `q_n` of `eq:qn`: `√(log n / r_n)` for `d = 2` and `log n / r_n` for `d ≥ 3`. -/
noncomputable def sourceRate (d : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  if d = 2 then Real.sqrt (Real.log n / sourceRadius d ε n) else Real.log n / sourceRadius d ε n

/-- `sourceRadius` is the radius used by the proofs. -/
private lemma sourceRadius_eq (d : ℕ) (ε : ℝ) (n : ℕ) : sourceRadius d ε n = radius d ε n := rfl

/-- `sourceRate` is the rate used by the proofs. -/
private lemma sourceRate_eq (d : ℕ) (ε : ℝ) (n : ℕ) : sourceRate d ε n = qrate d ε n := rfl

/-- In the plane, `r_n q_n^{1/2} = r_n^{3/4} (log n)^{1/4}`. -/
private lemma radius_mul_qrate_sqrt (hd : d = 2) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 2 ≤ n) :
    radius d ε n * qrate d ε n ^ ((1 : ℝ) / d) =
      radius d ε n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4) := by
  have hd1 : 1 ≤ d := by omega
  rw [tk_rq_rpow hd1 hε hn]
  subst hd
  simp only [if_true]
  norm_num

/-- **`eq:envelopeplanar` at every point** (Section 6). Let `d = 2`, `0 < ε`, `Cin` a
constant. There are `C` and `n₀` such that for every path and every `n ≥ n₀` that satisfy the
inner-radius clause `|R_in(n) - r_n| ≤ Cin r_n q_n` and the local-time clause
`|ℓ~_n(y) - 2dε (r_n - |y|)_+| ≤ Cin r_n q_n^{1/d}` of `prop:inner` at every `y`,
`ℓ~_n(y) ≤ 2dε (b - |y|)_+ + C r_n^{3/4} (log n)^{1/4}` for **every** `y ∈ ℝ²`, `b = R_in(n)`. -/
theorem planar_envelope_all_points (hd : d = 2) {ε : ℝ} (hε : 0 < ε) (Cin : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      |innerRadius Y n - sourceRadius d ε n| ≤
        Cin * sourceRadius d ε n * sourceRate d ε n →
      (∀ y : EuclideanSpace ℝ (Fin d),
        |cellLocalTime Y n y - 2 * d * ε * max (sourceRadius d ε n - ‖y‖) 0| ≤
          Cin * sourceRadius d ε n * sourceRate d ε n ^ ((1 : ℝ) / d)) →
      ∀ y : EuclideanSpace ℝ (Fin d), cellLocalTime Y n y ≤
        2 * d * ε * max (innerRadius Y n - ‖y‖) 0 +
          C * (sourceRadius d ε n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (tk_qrate_le_one hd1 hε)
  set Ci : ℝ := max Cin 0 with hCi
  have hCi0 : 0 ≤ Ci := le_max_right _ _
  have hdε : 0 ≤ 2 * (d : ℝ) * ε := by positivity
  refine ⟨(2 * d * ε + 1) * Ci + 1, by positivity, max N 2, ?_⟩
  intro Y n hn h1 h3 y
  have hnN : N ≤ n := le_of_max_le_left hn
  have hn2 : 2 ≤ n := le_of_max_le_right hn
  have hq1 : qrate d ε n ≤ 1 := hN n hnN
  have hq0' : 0 < qrate d ε n := co_qrate_pos hd1 hε hn2
  have hq0 : 0 ≤ qrate d ε n := hq0'.le
  have hr := radius_pos hd1 hε (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hqq : qrate d ε n ≤ qrate d ε n ^ ((1 : ℝ) / d) := by
    have h1' : (1 : ℝ) / d ≤ 1 := by
      rw [div_le_one hd0]
      exact_mod_cast hd1
    calc qrate d ε n = qrate d ε n ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ qrate d ε n ^ ((1 : ℝ) / d) := Real.rpow_le_rpow_of_exponent_ge hq0' hq1 h1'
  have hqd : 0 ≤ qrate d ε n ^ ((1 : ℝ) / d) := Real.rpow_nonneg hq0 _
  have hrq := radius_mul_qrate_sqrt hd hε hn2
  have h1' : |innerRadius Y n - radius d ε n| ≤ Cin * radius d ε n * qrate d ε n := h1
  have hb1 : |innerRadius Y n - radius d ε n| ≤ Ci * radius d ε n * qrate d ε n :=
    h1'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hr.le) hq0)
  have h3' := h3 y
  have h3'' : |cellLocalTime Y n y - 2 * d * ε * max (radius d ε n - ‖y‖) 0| ≤
      Cin * radius d ε n * qrate d ε n ^ ((1 : ℝ) / d) := h3'
  have hb3 : cellLocalTime Y n y - 2 * d * ε * max (radius d ε n - ‖y‖) 0 ≤
      Ci * (radius d ε n * qrate d ε n ^ ((1 : ℝ) / d)) := by
    refine (le_abs_self _).trans (h3''.trans ?_)
    calc Cin * radius d ε n * qrate d ε n ^ ((1 : ℝ) / d)
        = Cin * (radius d ε n * qrate d ε n ^ ((1 : ℝ) / d)) := by ring
      _ ≤ Ci * (radius d ε n * qrate d ε n ^ ((1 : ℝ) / d)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hr.le hqd)
  have hcone : max (radius d ε n - ‖y‖) 0 ≤
      max (innerRadius Y n - ‖y‖) 0 + |innerRadius Y n - radius d ε n| := by
    refine max_le ?_ (add_nonneg (le_max_right _ _) (abs_nonneg _))
    have h5 : innerRadius Y n - ‖y‖ ≤ max (innerRadius Y n - ‖y‖) 0 := le_max_left _ _
    have h6 : radius d ε n - innerRadius Y n ≤ |innerRadius Y n - radius d ε n| := by
      rw [← abs_neg, neg_sub]
      exact le_abs_self _
    linarith
  have hrq' : radius d ε n * qrate d ε n ≤ radius d ε n * qrate d ε n ^ ((1 : ℝ) / d) :=
    mul_le_mul_of_nonneg_left hqq hr.le
  have hP : 0 ≤ radius d ε n * qrate d ε n ^ ((1 : ℝ) / d) := mul_nonneg hr.le hqd
  have hsplit : 2 * d * ε * max (radius d ε n - ‖y‖) 0 ≤
      2 * d * ε * max (innerRadius Y n - ‖y‖) 0 +
        2 * d * ε * (Ci * (radius d ε n * qrate d ε n ^ ((1 : ℝ) / d))) := by
    have h7 : |innerRadius Y n - radius d ε n| ≤
        Ci * (radius d ε n * qrate d ε n ^ ((1 : ℝ) / d)) := by
      refine hb1.trans ?_
      calc Ci * radius d ε n * qrate d ε n = Ci * (radius d ε n * qrate d ε n) := by ring
        _ ≤ Ci * (radius d ε n * qrate d ε n ^ ((1 : ℝ) / d)) :=
            mul_le_mul_of_nonneg_left hrq' hCi0
    have h8 : max (radius d ε n - ‖y‖) 0 ≤ max (innerRadius Y n - ‖y‖) 0 +
        Ci * (radius d ε n * qrate d ε n ^ ((1 : ℝ) / d)) := by linarith
    have := mul_le_mul_of_nonneg_left h8 hdε
    linarith
  have hfin : cellLocalTime Y n y ≤ 2 * d * ε * max (innerRadius Y n - ‖y‖) 0 +
      (2 * d * ε + 1) * Ci * (radius d ε n * qrate d ε n ^ ((1 : ℝ) / d)) := by
    nlinarith [hb3, hsplit]
  have hX : 0 ≤ radius d ε n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4) := by
    rw [← hrq]
    exact hP
  rw [← hrq] at hX
  show cellLocalTime Y n y ≤ 2 * d * ε * max (innerRadius Y n - ‖y‖) 0 +
    ((2 * d * ε + 1) * Ci + 1) * (radius d ε n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4))
  rw [← hrq]
  nlinarith [hfin, hP]


/-- **The local time at every site of the plane** (Section 7, planar Step 1). Let `d = 2`, `0 < ε`,
and constants `C₀`, `C₁`. There are `C` and `n₀` such that for every path from the origin with
unit steps and every `n ≥ n₀` with the maximal local time `M_n ≤ C₀ n^{1/(d+1)}` and the
approximation `|ℓ~_n(y) - U_{D_n}(y)| ≤ C₁ (√M_n log (n + 2) + log (n + 2))` for `|y| ≤ 2n`
(`eq:approx` with `d = 2`), **every** site `x` satisfies, with `b = R_in(n)` and
`w = R_out(n) - b + 2√d`,
`ℓ_n(x) ≤ 2dε (b - |x|)_+ + C w + C √r_n log n`. -/
theorem planar_localtime_all_sites (hd : d = 2) {ε : ℝ} (hε : 0 < ε) (C₀ C₁ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      (∀ j, euclidNorm (Y j) ≤ j) →
      (maxLocalTime Y n : ℝ) ≤ C₀ * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) →
      (∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
        |cellLocalTime Y n y - potential d ε (cellSet Y n) y| ≤
          C₁ * (Real.sqrt (maxLocalTime Y n) * Real.log ((n : ℝ) + 2) +
            Real.log ((n : ℝ) + 2))) →
      ∀ x : Site d, (localTime Y n x : ℝ) ≤
        2 * d * ε * max (innerRadius Y n - euclidNorm x) 0 +
          C * (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) +
          C * (Real.sqrt (sourceRadius d ε n) * Real.log n) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  obtain ⟨a, ha, hra⟩ := tk_radius_eq hd1 hε
  obtain ⟨n₁, hn₁⟩ := hx_scales hd1 hε 1
  set C₀' : ℝ := max (C₀ / a) 0 with hC₀'
  have hC₀'0 : 0 ≤ C₀' := le_max_right _ _
  set Cδ : ℝ := |C₁| * (2 * Real.sqrt C₀' + 2) with hCδ
  have hCδ0 : 0 ≤ Cδ := by positivity
  have hdε : 0 ≤ 2 * (d : ℝ) * ε := by positivity
  refine ⟨max (2 * d * ε) Cδ + 1, by positivity, max n₁ 3, ?_⟩
  intro Y n hn hYn hmax hglob x
  have hn₁n : n₁ ≤ n := le_of_max_le_left hn
  have hn3 : 3 ≤ n := le_of_max_le_right hn
  obtain ⟨hr, hlr, -⟩ := hn₁ n hn₁n
  obtain ⟨hlg1, hLlg⟩ := hx_log_facts (n := n) hn3
  have hL1 : 1 ≤ Real.log ((n : ℝ) + 2) := CERW.Support.Law.one_le_log_add_two (by omega)
  have hlg0 : 0 ≤ Real.log n := by linarith
  have hr1 : 1 ≤ radius d ε n := by linarith
  have hsr : 1 ≤ Real.sqrt (radius d ε n) := Real.one_le_sqrt.mpr hr1
  have hM : (maxLocalTime Y n : ℝ) ≤ C₀' * radius d ε n := by
    have h1 : (n : ℝ) ^ ((1 : ℝ) / (d + 1)) = radius d ε n / a := by
      rw [hra n]
      field_simp
    calc (maxLocalTime Y n : ℝ) ≤ C₀ * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := hmax
      _ = (C₀ / a) * radius d ε n := by rw [h1]; field_simp
      _ ≤ C₀' * radius d ε n := mul_le_mul_of_nonneg_right (le_max_left _ _) hr.le
  have hδ : C₁ * (Real.sqrt (maxLocalTime Y n) * Real.log ((n : ℝ) + 2) +
      Real.log ((n : ℝ) + 2)) ≤ Cδ * (Real.sqrt (radius d ε n) * Real.log n) := by
    have hsM : Real.sqrt (maxLocalTime Y n) ≤
        Real.sqrt C₀' * Real.sqrt (radius d ε n) := by
      rw [← Real.sqrt_mul hC₀'0]
      exact Real.sqrt_le_sqrt hM
    have h1 : Real.sqrt (maxLocalTime Y n) * Real.log ((n : ℝ) + 2) +
        Real.log ((n : ℝ) + 2) ≤
        (Real.sqrt C₀' * Real.sqrt (radius d ε n)) * (2 * Real.log n) +
          2 * Real.log n := by
      have := mul_le_mul hsM hLlg (by linarith) (by positivity)
      linarith
    have h2 : (Real.sqrt C₀' * Real.sqrt (radius d ε n)) * (2 * Real.log n) +
        2 * Real.log n ≤
        (2 * Real.sqrt C₀' + 2) * (Real.sqrt (radius d ε n) * Real.log n) := by
      nlinarith [mul_le_mul_of_nonneg_right hsr hlg0]
    have hnn : 0 ≤ Real.sqrt (maxLocalTime Y n) * Real.log ((n : ℝ) + 2) +
        Real.log ((n : ℝ) + 2) := by positivity
    calc C₁ * (Real.sqrt (maxLocalTime Y n) * Real.log ((n : ℝ) + 2) +
          Real.log ((n : ℝ) + 2))
        ≤ |C₁| * (Real.sqrt (maxLocalTime Y n) * Real.log ((n : ℝ) + 2) +
          Real.log ((n : ℝ) + 2)) := mul_le_mul_of_nonneg_right (le_abs_self _) hnn
      _ ≤ |C₁| * ((2 * Real.sqrt C₀' + 2) * (Real.sqrt (radius d ε n) * Real.log n)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg _)
      _ = Cδ * (Real.sqrt (radius d ε n) * Real.log n) := by rw [hCδ]; ring
  have hw : 0 < maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d := by
    have := innerRadius_le hd1 Y n
    have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd1)
    linarith
  have hsrlg : 0 ≤ Real.sqrt (radius d ε n) * Real.log n :=
    mul_nonneg (Real.sqrt_nonneg _) hlg0
  have hCm : 2 * (d : ℝ) * ε ≤ max (2 * d * ε) Cδ + 1 := by
    have := le_max_left (2 * (d : ℝ) * ε) Cδ
    linarith
  have hCm' : Cδ ≤ max (2 * d * ε) Cδ + 1 := by
    have := le_max_right (2 * (d : ℝ) * ε) Cδ
    linarith
  by_cases hx : euclidNorm x ≤ 2 * n
  · have hxn : ‖toSpace x‖ ≤ 2 * n := by rw [norm_toSpace]; exact hx
    have h := hglob (toSpace x) hxn
    rw [cellLocalTime_of_mem_cell _ _ (toSpace_mem_cell x)] at h
    have hDmeas := CERW.Support.Occupation.measurableSet_cellSet Y n
    have hDb : Bornology.IsBounded (cellSet Y n) :=
      Metric.isBounded_ball.subset (CERW.Support.Occupation.cellSet_subset_ball hd1 Y n)
    have hEmeas : MeasurableSet (cellSet Y n \ Metric.ball 0 (innerRadius Y n)) :=
      hDmeas.diff measurableSet_ball
    have hsplit := ev_potential_split hd2 ε hDmeas hDb (innerRadius_nonneg Y n)
      (ball_innerRadius_subset hd1 Y n) (toSpace x)
    have hann := annulus_potential_le hd2 hε hw hEmeas (sdiff_subset_annulus hd1 Y n)
      (toSpace x)
    rw [norm_toSpace] at hsplit
    have hUE := (abs_le.mp hann).2
    have hl := (abs_le.mp h).2
    have hw0 := hw.le
    have e1 : 2 * (d : ℝ) * ε * (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) ≤
        (max (2 * d * ε) Cδ + 1) * (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) :=
      mul_le_mul_of_nonneg_right hCm hw0
    have e2 : Cδ * (Real.sqrt (radius d ε n) * Real.log n) ≤
        (max (2 * d * ε) Cδ + 1) * (Real.sqrt (radius d ε n) * Real.log n) :=
      mul_le_mul_of_nonneg_right hCm' hsrlg
    show (localTime Y n x : ℝ) ≤ 2 * d * ε * max (innerRadius Y n - euclidNorm x) 0 +
      (max (2 * d * ε) Cδ + 1) * (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) +
        (max (2 * d * ε) Cδ + 1) * (Real.sqrt (radius d ε n) * Real.log n)
    linarith
  · have hx' : 2 * (n : ℝ) < euclidNorm x := not_le.mp hx
    have hz : localTime Y n x = 0 := by
      by_contra hne
      have hmem : x ∈ departureRange Y n := mem_departureRange_iff.mpr (Nat.pos_of_ne_zero hne)
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hmem
      have h1 := hYn j
      have hjn : (j : ℝ) < n := by exact_mod_cast Finset.mem_range.mp hj
      linarith [Nat.cast_nonneg (α := ℝ) n]
    rw [hz, Nat.cast_zero]
    have h0 : 0 ≤ 2 * (d : ℝ) * ε * max (innerRadius Y n - euclidNorm x) 0 :=
      mul_nonneg hdε (le_max_right _ _)
    have hCpos : 0 < max (2 * (d : ℝ) * ε) Cδ + 1 := by positivity
    have e1 : 0 ≤ (max (2 * (d : ℝ) * ε) Cδ + 1) *
        (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) := mul_nonneg hCpos.le hw.le
    have e2 : 0 ≤ (max (2 * (d : ℝ) * ε) Cδ + 1) *
        (Real.sqrt (radius d ε n) * Real.log n) := mul_nonneg hCpos.le hsrlg
    show (0 : ℝ) ≤ 2 * d * ε * max (innerRadius Y n - euclidNorm x) 0 +
      (max (2 * d * ε) Cδ + 1) * (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) +
        (max (2 * d * ε) Cδ + 1) * (Real.sqrt (radius d ε n) * Real.log n)
    linarith

/-- **The local times of the plane at every site, with high probability**: for `d = 2`,
`0 < ε < 1/2` and `p > 0` there are constants `C` and `Cp`, chosen before the probability space,
the walk and `n`, such that for every centrally excited random walk and every `n ≥ 2`, with
probability at least `1 - Cp n^{-p}` every site `x ∈ ℤ²` satisfies
`ℓ_n(x) ≤ 2dε (b - |x|)_+ + C w + C √r_n log n`, `b = R_in(n)`,
`w = R_out(n) - b + 2√d`. -/
theorem planar_localtime_all_sites_prob (hd : d = 2) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    ∃ C Cp : ℝ, 0 < C ∧ 0 < Cp ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ ∀ x : Site d, (localTime (fun j => X j ω) n x : ℝ) ≤
            2 * d * ε * max (innerRadius (fun j => X j ω) n - euclidNorm x) 0 +
              C * (maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n +
                2 * Real.sqrt d) +
              C * (Real.sqrt (sourceRadius d ε n) * Real.log n)} ≤
          ENNReal.ofReal (Cp * (n : ℝ) ^ (-p)) := by
  obtain ⟨C₀, C₁, Cf, hC₀, hC₁, hCf, hfl⟩ := exists_pathFacts_prob (by omega : 2 ≤ d) hε hεd hp
  obtain ⟨C, hC, n₀, hdet⟩ := planar_localtime_all_sites hd hε C₀ C₁
  have hNp : 0 < ((n₀ : ℝ) + 1) ^ p := Real.rpow_pos_of_pos (by positivity) p
  refine ⟨C, Cf + ((n₀ : ℝ) + 1) ^ p, hC, by positivity, ?_⟩
  intro Ω _ μ _ X hX n hn2
  by_cases hnb : n₀ ≤ n
  · refine le_trans (measure_mono ?_) ((hfl μ X hX n hn2).trans
      (ENNReal.ofReal_le_ofReal ?_))
    · intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      intro hPF
      apply hω
      obtain ⟨hstart, hstep, hmaxloc, -, hglob, -, -⟩ := hPF
      have hYn := CERW.Support.Occupation.euclidNorm_le_of_steps (fun j => X j ω) hstart hstep
      refine hdet _ n hnb hYn hmaxloc ?_
      intro y hy
      have := hglob y hy
      rw [if_pos hd] at this
      exact this
    · have : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      nlinarith
  · exact (prob_le_one).trans (one_le_ofReal_mul_rpow hp (by omega) (not_le.mp hnb)
      (by linarith))

/-- **The planar envelope at every point, with high probability.** For `d = 2`, `0 < ε < 1/2` and
`p > 0` there are constants `C`, `Cp` such that for every centrally excited random walk and every
`n ≥ 2`, with probability at least `1 - Cp n^{-p}`, every `y ∈ ℝ²` satisfies
`ℓ~_n(y) ≤ 2dε (b - |y|)_+ + C r_n^{3/4} (log n)^{1/4}` with `b = R_in(n)`. The proof applies the
proved `prop:inner` (the inner-radius and local-time clauses) with `planar_envelope_all_points`. -/
theorem planar_envelope_all_points_prob (hd : d = 2) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    ∃ C Cp : ℝ, 0 < C ∧ 0 < Cp ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ ∀ y : EuclideanSpace ℝ (Fin d), cellLocalTime (fun j => X j ω) n y ≤
            2 * d * ε * max (innerRadius (fun j => X j ω) n - ‖y‖) 0 +
              C * (sourceRadius d ε n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4))} ≤
          ENNReal.ofReal (Cp * (n : ℝ) ^ (-p)) := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨Cin, hCin, hin⟩ := CERW.Frozen.inner_radius hd2 ε hε hεd p hp
  obtain ⟨C, hC, n₀, hdet⟩ := planar_envelope_all_points hd hε Cin
  have hNp : 0 < ((n₀ : ℝ) + 1) ^ p := Real.rpow_pos_of_pos (by positivity) p
  refine ⟨C, Cin + ((n₀ : ℝ) + 1) ^ p, hC, by positivity, ?_⟩
  intro Ω _ μ _ X hX n hn2
  by_cases hnb : n₀ ≤ n
  · refine le_trans (measure_mono ?_) ((hin μ X hX n hn2).trans
      (ENNReal.ofReal_le_ofReal ?_))
    · intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      intro hABC
      apply hω
      obtain ⟨hA, -, hC3⟩ := hABC
      exact fun y => hdet _ n hnb hA hC3 y
    · have : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      nlinarith
  · exact (prob_le_one).trans (one_le_ofReal_mul_rpow hp (by omega) (not_le.mp hnb)
      (by linarith))


/-! ## The origin's cell, and consumers of the displays at an actual walk -/

/-- For a path from the origin and `n ≥ 1`, the cell of the origin lies in `D_n`, so the ball
`B(0, 1/2)` lies in `D_n`. -/
lemma ball_half_subset_cellSet (Y : ℕ → Site d) (n : ℕ) (hn : 1 ≤ n) (h0 : Y 0 = 0) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2) ⊆ cellSet Y n := by
  intro v hv
  have h0mem : (0 : Site d) ∈ departureRange Y n :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), h0⟩
  refine Set.mem_iUnion₂.mpr ⟨0, h0mem, ?_⟩
  intro i
  have h1 : ‖v i‖ ≤ ‖v‖ := PiLp.norm_apply_le v i
  have h2 : ‖v‖ < 1 / 2 := mem_ball_zero_iff.mp hv
  rw [Real.norm_eq_abs] at h1
  have h3 := abs_lt.mp (lt_of_le_of_lt h1 h2)
  simp only [Pi.zero_apply, Int.cast_zero]
  constructor <;> linarith [h3.1, h3.2]

/-- For a path from the origin and `n ≥ 1` in dimension `d ≥ 1`, the inner radius is at least
`1/2`; in particular the origin is an interior point of `D_n`. -/
lemma half_le_innerRadius (hd : 1 ≤ d) (Y : ℕ → Site d) (n : ℕ) (hn : 1 ≤ n) (h0 : Y 0 = 0) :
    1 / 2 ≤ innerRadius Y n := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  unfold innerRadius
  refine le_csInf ?_ ?_
  · obtain ⟨v, hv⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin d))
      (show 0 ≤ maxRadius Y n + Real.sqrt d by
        have := gd_maxRadius_nonneg Y n
        have := Real.sqrt_nonneg (d : ℝ)
        linarith)
    refine ⟨‖v‖, v, ?_, rfl⟩
    intro hvD
    have h := CERW.Support.Occupation.norm_le_of_mem_cellSet Y n hvD
    have := Real.sqrt_nonneg (d : ℝ)
    rw [hv] at h
    have hd0 : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    linarith
  · rintro _ ⟨y, hy, rfl⟩
    by_contra hlt
    push Not at hlt
    exact hy (ball_half_subset_cellSet Y n hn h0 (mem_ball_zero_iff.mpr hlt))

/-- **Consumer of `eq:potential-convolution` and `eq:envelopehigh`.** For `d ≥ 3` and `0 < ε < 1/d`
there are a probability space carrying centrally excited random walk, constants `Cc`, `Ce`, a time
`n ≥ 2` and a sample point `ω` with the walk at the origin at time zero, at which the displays hold
at every point, with inner radius at least `1/2`; so the origin is an interior point
(`0 < (b - |0|)_+`) at which the first envelope is a genuine cone estimate, and every point
`(b + 1) e₁` is an exterior point at which the second envelope holds. -/
theorem exists_realization_envelope_high (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site d), IsCERW μ ε X ∧ ∃ Cc Ce : ℝ, 0 < Cc ∧ 0 < Ce ∧
        ∃ (n : ℕ) (ω : Ω), 2 ≤ n ∧ X 0 ω = 0 ∧
          EnvelopeHighDisplays d ε Cc Ce (fun j => X j ω) n ∧
          1 / 2 ≤ innerRadius (fun j => X j ω) n ∧
          0 < max (innerRadius (fun j => X j ω) n - ‖(0 : EuclideanSpace ℝ (Fin d))‖) 0 ∧
          ∀ y : EuclideanSpace ℝ (Fin d), innerRadius (fun j => X j ω) n + 1 ≤ ‖y‖ →
            cellLocalTime (fun j => X j ω) n y ≤
              Ce * (positivePotential d ε (cellSet (fun j => X j ω) n \
                Metric.ball 0 (innerRadius (fun j => X j ω) n)) y + Real.log n) := by
  obtain ⟨Ω, hΩ, μ, hμ, X, hX⟩ := CERW.Support.Law.exists_isCERW (by omega : 1 ≤ d) hε.le hεd
  obtain ⟨Cc, Ce, Cp, hCc, hCe, hCp, h⟩ := envelope_high_prob.{0} hd hε hεd (p := 1) one_pos
  refine ⟨Ω, hΩ, μ, hμ, X, hX, Cc, Ce, hCc, hCe, ?_⟩
  set n : ℕ := ⌈Cp⌉₊ + 2 with hn
  have hn2 : 2 ≤ n := by omega
  have hCn : Cp * (n : ℝ) ^ (-(1 : ℝ)) < 1 := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_lt_one hn0]
    have := Nat.le_ceil Cp
    have hn' : (n : ℝ) = (⌈Cp⌉₊ : ℝ) + 2 := by rw [hn]; push_cast; ring
    linarith
  have hbad := (h μ X hX n hn2).trans_lt (by rw [ENNReal.ofReal_lt_one]; exact hCn)
  have hex : ∃ ω, EnvelopeHighDisplays d ε Cc Ce (fun j => X j ω) n ∧ X 0 ω = 0 := by
    by_contra hno
    push Not at hno
    have hsub : (Set.univ : Set Ω) ⊆
        {ω | ¬ EnvelopeHighDisplays d ε Cc Ce (fun j => X j ω) n} ∪ {ω | X 0 ω ≠ 0} := by
      intro ω _
      by_cases hD : EnvelopeHighDisplays d ε Cc Ce (fun j => X j ω) n
      · exact Or.inr (hno ω hD)
      · exact Or.inl hD
    have h1 := (measure_mono (μ := μ) hsub).trans (measure_union_le _ _)
    rw [measure_univ, hX.start, add_zero] at h1
    exact absurd (h1.trans_lt hbad) (lt_irrefl _)
  obtain ⟨ω, hD, h0⟩ := hex
  have hb := half_le_innerRadius (by omega : 1 ≤ d) (fun j => X j ω) n (by omega) h0
  refine ⟨n, ω, hn2, h0, hD, hb, ?_, ?_⟩
  · rw [norm_zero, sub_zero]
    exact lt_max_of_lt_left (by linarith)
  · intro y hy
    exact (hD y).2.2 (by linarith)


/-- **Consumer of the layer-cake identity.** For `d ≥ 3` the unit ball `E = B(0,1)` is a bounded
measurable set of positive volume that contains the singular evaluation point `y = 0`; the identity
holds for it, with both sides finite. (At `v = y` the integrand `|v - y|^{2-d}` reads `0` in the
formalization while the layer integral diverges; this is the null set discarded in the proof.) -/
theorem layer_cake_eq_ball (hd : 3 ≤ d) :
    0 < volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ∧
      (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∧
      IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v - 0‖ ^ (2 - (d : ℝ)))
        (Metric.ball 0 1) ∧
      ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1, ‖v - 0‖ ^ (2 - (d : ℝ)) =
        ((d : ℝ) - 2) * ∫ t in Set.Ioi (0 : ℝ),
          (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∩ Metric.ball 0 t)).toReal *
            t ^ (1 - (d : ℝ)) := by
  have h := layer_cake_eq hd (measurableSet_ball (x := (0 : EuclideanSpace ℝ (Fin d)))
    (ε := 1)) Metric.isBounded_ball (0 : EuclideanSpace ℝ (Fin d))
  exact ⟨Metric.measure_ball_pos _ _ one_pos, Metric.mem_ball_self one_pos, h.1, h.2.2⟩

/-- **Consumer of the planar displays at an actual walk.** In the plane with `ε = 1/4` there are a
probability space carrying centrally excited random walk, constants `C`, `Cs`, a time `n ≥ 2` and a
sample point `ω` starting at the origin such that every point `y` satisfies the planar envelope
and every site `x` the local-time display, with inner radius at least `1/2`, so the origin is an
interior point of the range, and every `y` with `|y| ≥ b + 1` is an exterior point. -/
theorem exists_realization_planar_displays :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2), IsCERW μ (1 / 4 : ℝ) X ∧ ∃ C Cs : ℝ, 0 < C ∧ 0 < Cs ∧
        ∃ (n : ℕ) (ω : Ω), 2 ≤ n ∧ X 0 ω = 0 ∧
          1 / 2 ≤ innerRadius (fun j => X j ω) n ∧
          (∀ y : EuclideanSpace ℝ (Fin 2), cellLocalTime (fun j => X j ω) n y ≤
            2 * (2 : ℕ) * (1 / 4 : ℝ) * max (innerRadius (fun j => X j ω) n - ‖y‖) 0 +
              C * (sourceRadius 2 (1 / 4 : ℝ) n ^ ((3 : ℝ) / 4) *
                Real.log n ^ ((1 : ℝ) / 4))) ∧
          (∀ x : Site 2, (localTime (fun j => X j ω) n x : ℝ) ≤
            2 * (2 : ℕ) * (1 / 4 : ℝ) * max (innerRadius (fun j => X j ω) n - euclidNorm x) 0 +
              Cs * (maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n +
                2 * Real.sqrt (2 : ℕ)) +
              Cs * (Real.sqrt (sourceRadius 2 (1 / 4 : ℝ) n) * Real.log n)) := by
  have hd : (2 : ℕ) = 2 := rfl
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  have hεd : (1 / 4 : ℝ) < 1 / ((2 : ℕ) : ℝ) := by norm_num
  obtain ⟨Ω, hΩ, μ, hμ, X, hX⟩ := CERW.Support.Law.exists_isCERW (d := 2) (by omega) hε.le hεd
  obtain ⟨C, Cp, hC, hCp, h1⟩ :=
    planar_envelope_all_points_prob (d := 2) rfl hε hεd (p := 1) one_pos
  obtain ⟨Cs, Cq, hCs, hCq, h2⟩ :=
    planar_localtime_all_sites_prob (d := 2) rfl hε hεd (p := 1) one_pos
  refine ⟨Ω, hΩ, μ, hμ, X, hX, C, Cs, hC, hCs, ?_⟩
  set n : ℕ := ⌈Cp + Cq⌉₊ + 2 with hn
  have hn2 : 2 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn' : (n : ℝ) = (⌈Cp + Cq⌉₊ : ℝ) + 2 := by rw [hn]; push_cast; ring
  have hCn : Cp * (n : ℝ) ^ (-(1 : ℝ)) + Cq * (n : ℝ) ^ (-(1 : ℝ)) < 1 := by
    rw [Real.rpow_neg_one, ← add_mul, ← div_eq_mul_inv, div_lt_one hn0]
    have := Nat.le_ceil (Cp + Cq)
    linarith
  have hb1 := h1 μ X hX n hn2
  have hb2 := h2 μ X hX n hn2
  have hsum : μ {ω | ¬ ∀ y : EuclideanSpace ℝ (Fin 2), cellLocalTime (fun j => X j ω) n y ≤
        2 * (2 : ℕ) * (1 / 4 : ℝ) * max (innerRadius (fun j => X j ω) n - ‖y‖) 0 +
          C * (sourceRadius 2 (1 / 4 : ℝ) n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4))} +
      μ {ω | ¬ ∀ x : Site 2, (localTime (fun j => X j ω) n x : ℝ) ≤
        2 * (2 : ℕ) * (1 / 4 : ℝ) * max (innerRadius (fun j => X j ω) n - euclidNorm x) 0 +
          Cs * (maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n +
            2 * Real.sqrt (2 : ℕ)) +
          Cs * (Real.sqrt (sourceRadius 2 (1 / 4 : ℝ) n) * Real.log n)} < 1 := by
    refine (add_le_add hb1 hb2).trans_lt ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_lt_one]
    linarith
  have hex : ∃ ω, X 0 ω = 0 ∧
      (∀ y : EuclideanSpace ℝ (Fin 2), cellLocalTime (fun j => X j ω) n y ≤
        2 * (2 : ℕ) * (1 / 4 : ℝ) * max (innerRadius (fun j => X j ω) n - ‖y‖) 0 +
          C * (sourceRadius 2 (1 / 4 : ℝ) n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4))) ∧
      (∀ x : Site 2, (localTime (fun j => X j ω) n x : ℝ) ≤
        2 * (2 : ℕ) * (1 / 4 : ℝ) * max (innerRadius (fun j => X j ω) n - euclidNorm x) 0 +
          Cs * (maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n +
            2 * Real.sqrt (2 : ℕ)) +
          Cs * (Real.sqrt (sourceRadius 2 (1 / 4 : ℝ) n) * Real.log n)) := by
    by_contra hno
    push Not at hno
    have hsub : (Set.univ : Set Ω) ⊆
        ({ω | ¬ ∀ y : EuclideanSpace ℝ (Fin 2), cellLocalTime (fun j => X j ω) n y ≤
          2 * (2 : ℕ) * (1 / 4 : ℝ) * max (innerRadius (fun j => X j ω) n - ‖y‖) 0 +
            C * (sourceRadius 2 (1 / 4 : ℝ) n ^ ((3 : ℝ) / 4) *
              Real.log n ^ ((1 : ℝ) / 4))} ∪
        {ω | ¬ ∀ x : Site 2, (localTime (fun j => X j ω) n x : ℝ) ≤
          2 * (2 : ℕ) * (1 / 4 : ℝ) * max (innerRadius (fun j => X j ω) n - euclidNorm x) 0 +
            Cs * (maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n +
              2 * Real.sqrt (2 : ℕ)) +
            Cs * (Real.sqrt (sourceRadius 2 (1 / 4 : ℝ) n) * Real.log n)}) ∪
        {ω | X 0 ω ≠ 0} := by
      intro ω _
      by_cases h0 : X 0 ω = 0
      · by_cases hA : ∀ y : EuclideanSpace ℝ (Fin 2), cellLocalTime (fun j => X j ω) n y ≤
          2 * (2 : ℕ) * (1 / 4 : ℝ) * max (innerRadius (fun j => X j ω) n - ‖y‖) 0 +
            C * (sourceRadius 2 (1 / 4 : ℝ) n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4))
        · refine Or.inl (Or.inr ?_)
          intro hall
          obtain ⟨x, hx⟩ := hno ω h0 hA
          exact absurd (hall x) (not_le.mpr hx)
        · exact Or.inl (Or.inl hA)
      · exact Or.inr h0
    have h3 := (measure_mono (μ := μ) hsub).trans (measure_union_le _ _)
    have h4 := h3.trans (add_le_add (measure_union_le _ _) le_rfl)
    rw [measure_univ, hX.start, add_zero] at h4
    exact absurd (h4.trans_lt hsum) (lt_irrefl _)
  obtain ⟨ω, h0, hA, hB⟩ := hex
  exact ⟨n, ω, hn2, h0, half_le_innerRadius (by omega) _ n (by omega) h0, hA, hB⟩


/-! ## The exact scale of the global approximation -/

/-- **`eq:global` at the exact scale** (Section 6). Let `d ≥ 2`, `0 < ε` and constants `C₀`, `C₁`.
There are `C` and `n₀` such that the following holds for every path and every `n ≥ n₀` whose
maximal local time satisfies `M_n ≤ C₀ n^{1/(d+1)}` and whose local time approximates the
potential (`eq:approx`), for every `y` with `|y| ≤ 2n`, by
`|ℓ~_n(y) - U_{D_n}(y)| ≤ C₁ (√M_n log (n + 2) + log (n + 2))` if `d = 2` and
`≤ C₁ (√(M_n log (n + 2)) + log (n + 2))` if `d ≥ 3`: every `y` with `|y| ≤ 2n` satisfies
`|ℓ~_n(y) - U_{D_n}(y)| ≤ C √r_n log n` if `d = 2` and `≤ C √(r_n log n)` if `d ≥ 3`. The region
`|y| ≤ 2n` contains the ball `B(0, K r_n)` once `K r_n ≤ 2n`. -/
theorem global_approximation_scale (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (C₀ C₁ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      (maxLocalTime Y n : ℝ) ≤ C₀ * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) →
      (∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
        |cellLocalTime Y n y - potential d ε (cellSet Y n) y| ≤ C₁ *
          (if d = 2 then Real.sqrt (maxLocalTime Y n) * Real.log ((n : ℝ) + 2) +
              Real.log ((n : ℝ) + 2)
            else Real.sqrt (maxLocalTime Y n * Real.log ((n : ℝ) + 2)) +
              Real.log ((n : ℝ) + 2))) →
      ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
        |cellLocalTime Y n y - potential d ε (cellSet Y n) y| ≤
          C * (if d = 2 then Real.sqrt (sourceRadius d ε n) * Real.log n
            else Real.sqrt (sourceRadius d ε n * Real.log n)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨a, ha, hra⟩ := tk_radius_eq hd1 hε
  obtain ⟨n₁, hn₁⟩ := hx_scales hd1 hε 1
  set C₀' : ℝ := max (C₀ / a) 0 with hC₀'
  have hC₀'0 : 0 ≤ C₀' := le_max_right _ _
  set Cδ : ℝ := |C₁| * (Real.sqrt (2 * C₀') + 2) + |C₁| * (2 * Real.sqrt C₀' + 2) with hCδ
  have hCδ0 : 0 ≤ Cδ := by positivity
  refine ⟨Cδ + 1, by positivity, max n₁ 3, ?_⟩
  intro Y n hn hmax hglob y hy
  have hn₁n : n₁ ≤ n := le_of_max_le_left hn
  have hn3 : 3 ≤ n := le_of_max_le_right hn
  obtain ⟨hr, hlr, -⟩ := hn₁ n hn₁n
  obtain ⟨hlg1, hLlg⟩ := hx_log_facts (n := n) hn3
  have hL1 : 1 ≤ Real.log ((n : ℝ) + 2) := CERW.Support.Law.one_le_log_add_two (by omega)
  have hlg0 : 0 ≤ Real.log n := by linarith
  have hr1 : 1 ≤ radius d ε n := by linarith
  have hsr : 1 ≤ Real.sqrt (radius d ε n) := Real.one_le_sqrt.mpr hr1
  have hM : (maxLocalTime Y n : ℝ) ≤ C₀' * radius d ε n := by
    have h1 : (n : ℝ) ^ ((1 : ℝ) / (d + 1)) = radius d ε n / a := by
      rw [hra n]
      field_simp
    calc (maxLocalTime Y n : ℝ) ≤ C₀ * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := hmax
      _ = (C₀ / a) * radius d ε n := by rw [h1]; field_simp
      _ ≤ C₀' * radius d ε n := mul_le_mul_of_nonneg_right (le_max_left _ _) hr.le
  have h := hglob y hy
  by_cases h2 : d = 2
  · rw [if_pos h2] at h ⊢
    have hsM : Real.sqrt (maxLocalTime Y n) ≤
        Real.sqrt C₀' * Real.sqrt (radius d ε n) := by
      rw [← Real.sqrt_mul hC₀'0]
      exact Real.sqrt_le_sqrt hM
    have h1 : Real.sqrt (maxLocalTime Y n) * Real.log ((n : ℝ) + 2) +
        Real.log ((n : ℝ) + 2) ≤
        (Real.sqrt C₀' * Real.sqrt (radius d ε n)) * (2 * Real.log n) +
          2 * Real.log n := by
      have := mul_le_mul hsM hLlg (by linarith) (by positivity)
      linarith
    have h3 : (Real.sqrt C₀' * Real.sqrt (radius d ε n)) * (2 * Real.log n) +
        2 * Real.log n ≤
        (2 * Real.sqrt C₀' + 2) * (Real.sqrt (radius d ε n) * Real.log n) := by
      nlinarith [mul_le_mul_of_nonneg_right hsr hlg0]
    have hnn : 0 ≤ Real.sqrt (maxLocalTime Y n) * Real.log ((n : ℝ) + 2) +
        Real.log ((n : ℝ) + 2) := by positivity
    have hsrlg : 0 ≤ Real.sqrt (radius d ε n) * Real.log n :=
      mul_nonneg (Real.sqrt_nonneg _) hlg0
    refine h.trans ?_
    calc C₁ * (Real.sqrt (maxLocalTime Y n) * Real.log ((n : ℝ) + 2) +
          Real.log ((n : ℝ) + 2))
        ≤ |C₁| * (Real.sqrt (maxLocalTime Y n) * Real.log ((n : ℝ) + 2) +
          Real.log ((n : ℝ) + 2)) := mul_le_mul_of_nonneg_right (le_abs_self _) hnn
      _ ≤ |C₁| * ((2 * Real.sqrt C₀' + 2) * (Real.sqrt (radius d ε n) * Real.log n)) :=
          mul_le_mul_of_nonneg_left (h1.trans h3) (abs_nonneg _)
      _ ≤ (Cδ + 1) * (Real.sqrt (radius d ε n) * Real.log n) := by
          have : |C₁| * (2 * Real.sqrt C₀' + 2) ≤ Cδ + 1 := by
            rw [hCδ]
            have := mul_nonneg (abs_nonneg C₁) (Real.sqrt_nonneg (2 * C₀') |>.trans
              (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2)))
            nlinarith [abs_nonneg C₁, Real.sqrt_nonneg (2 * C₀')]
          calc _ = (|C₁| * (2 * Real.sqrt C₀' + 2)) * (Real.sqrt (radius d ε n) * Real.log n) :=
                by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right this hsrlg
  · rw [if_neg h2] at h ⊢
    have hlgr : Real.log n ≤ radius d ε n := by linarith
    have hrl : 0 ≤ radius d ε n * Real.log n := mul_nonneg hr.le hlg0
    have hs : Real.log n ≤ Real.sqrt (radius d ε n * Real.log n) := by
      refine Real.le_sqrt_of_sq_le ?_
      nlinarith [mul_le_mul_of_nonneg_right hlgr hlg0]
    have hML : maxLocalTime Y n * Real.log ((n : ℝ) + 2) ≤
        (2 * C₀') * (radius d ε n * Real.log n) := by
      have := mul_le_mul hM hLlg (by linarith) (by positivity)
      nlinarith
    have hs1 : Real.sqrt (maxLocalTime Y n * Real.log ((n : ℝ) + 2)) ≤
        Real.sqrt (2 * C₀') * Real.sqrt (radius d ε n * Real.log n) := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt hML
    have hsq0 : 0 ≤ Real.sqrt (radius d ε n * Real.log n) := Real.sqrt_nonneg _
    have h1 : Real.sqrt (maxLocalTime Y n * Real.log ((n : ℝ) + 2)) +
        Real.log ((n : ℝ) + 2) ≤
        (Real.sqrt (2 * C₀') + 2) * Real.sqrt (radius d ε n * Real.log n) := by
      nlinarith
    have hnn : 0 ≤ Real.sqrt (maxLocalTime Y n * Real.log ((n : ℝ) + 2)) +
        Real.log ((n : ℝ) + 2) := by positivity
    refine h.trans ?_
    calc C₁ * (Real.sqrt (maxLocalTime Y n * Real.log ((n : ℝ) + 2)) +
          Real.log ((n : ℝ) + 2))
        ≤ |C₁| * (Real.sqrt (maxLocalTime Y n * Real.log ((n : ℝ) + 2)) +
          Real.log ((n : ℝ) + 2)) := mul_le_mul_of_nonneg_right (le_abs_self _) hnn
      _ ≤ |C₁| * ((Real.sqrt (2 * C₀') + 2) * Real.sqrt (radius d ε n * Real.log n)) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ (Cδ + 1) * Real.sqrt (radius d ε n * Real.log n) := by
          have : |C₁| * (Real.sqrt (2 * C₀') + 2) ≤ Cδ + 1 := by
            rw [hCδ]
            nlinarith [abs_nonneg C₁, Real.sqrt_nonneg C₀',
              mul_nonneg (abs_nonneg C₁) (Real.sqrt_nonneg C₀')]
          calc _ = (|C₁| * (Real.sqrt (2 * C₀') + 2)) * Real.sqrt (radius d ε n * Real.log n) :=
                by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right this hsq0


/-- For every constant `K` the ball `B(0, K r_n)` lies in the ball `B(0, 2n)` for all large `n`,
because `r_n` has order `n^{1/(d+1)}`. -/
lemma eventually_mul_radius_le (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → K * sourceRadius d ε n ≤ 2 * n := by
  obtain ⟨a, ha, hra⟩ := tk_radius_eq hd hε
  refine ⟨⌈(K * a) ^ 2⌉₊ + 1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnn : (K * a) ^ 2 ≤ n := by
    have := Nat.le_ceil ((K * a) ^ 2)
    have h2 : ((⌈(K * a) ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hsq : |K * a| ≤ Real.sqrt n := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hnn
  have hroot : (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ≤ Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]
    refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hsr : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (by linarith)
  show K * radius d ε n ≤ 2 * n
  rw [hra n]
  calc K * (a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) = (K * a) * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
        ring
    _ ≤ |K * a| * Real.sqrt n := by
        refine mul_le_mul (le_abs_self _) hroot (Real.rpow_nonneg (by linarith) _)
          (abs_nonneg _)
    _ ≤ Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _)
    _ ≤ 2 * n := by linarith

/-- **`eq:global` on the ball `B(0, K r_n)`** (Section 6). For every `K`, the bound of
`global_approximation_scale` holds at every `y` with `|y| < K r_n`, for all large `n`. -/
theorem global_approximation_scale_ball (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (K C₀ C₁ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      (maxLocalTime Y n : ℝ) ≤ C₀ * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) →
      (∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
        |cellLocalTime Y n y - potential d ε (cellSet Y n) y| ≤ C₁ *
          (if d = 2 then Real.sqrt (maxLocalTime Y n) * Real.log ((n : ℝ) + 2) +
              Real.log ((n : ℝ) + 2)
            else Real.sqrt (maxLocalTime Y n * Real.log ((n : ℝ) + 2)) +
              Real.log ((n : ℝ) + 2))) →
      ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ < K * sourceRadius d ε n →
        |cellLocalTime Y n y - potential d ε (cellSet Y n) y| ≤
          C * (if d = 2 then Real.sqrt (sourceRadius d ε n) * Real.log n
            else Real.sqrt (sourceRadius d ε n * Real.log n)) := by
  obtain ⟨C, hC, n₀, h⟩ := global_approximation_scale hd hε C₀ C₁
  obtain ⟨n₁, hn₁⟩ := eventually_mul_radius_le (by omega : 1 ≤ d) hε K
  refine ⟨C, hC, max n₀ n₁, fun Y n hn hmax hglob y hy => ?_⟩
  exact h Y n (le_of_max_le_left hn) hmax hglob y
    ((hy.le).trans (hn₁ n (le_of_max_le_right hn)))


/-! ## Harmonicity of the planar potential and of the planar Newton field -/

open private mp_e mp_field mp_differentiableOn_field mp_potential_eq
  from CERW.Support.Outer.OuterRadius

/-- The Laplacian of a function composed with a linear isometry on the right is the Laplacian of
the function at the image point. -/
lemma laplacian_comp_linearIsometryEquiv {G H : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] (L : G ≃ₗᵢ[ℝ] H) (f : H → ℝ) (x : G) :
    Laplacian.laplacian (f ∘ L) x = Laplacian.laplacian f (L x) := by
  have h1 := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (f ∘ L) (stdOrthonormalBasis ℝ G)) x
  have h2 := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    ((stdOrthonormalBasis ℝ G).map L)) (L x)
  rw [h1, h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h3 : iteratedFDeriv ℝ 2 (f ∘ L) x =
      (iteratedFDeriv ℝ 2 f (L x)).compContinuousLinearMap fun _ => L.toContinuousLinearEquiv := by
    simp only [← iteratedFDerivWithin_univ]
    have := L.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
      (Set.mem_univ (L x)) 2
    simpa using this
  rw [h3]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, OrthonormalBasis.map_apply]
  congr 1
  funext j
  fin_cases j <;> simp

/-- Harmonicity at a point is transported by a linear isometry of the domain. -/
lemma harmonicAt_comp_linearIsometryEquiv {G H : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] (L : G ≃ₗᵢ[ℝ] H) {f : H → ℝ} {x : G}
    (h : InnerProductSpace.HarmonicAt f (L x)) : InnerProductSpace.HarmonicAt (f ∘ L) x := by
  refine ⟨h.1.comp x L.contDiff.contDiffAt, ?_⟩
  have hev : ∀ᶠ y in 𝓝 (L x), Laplacian.laplacian f y = 0 := h.2
  have hev' : ∀ᶠ y in 𝓝 x, Laplacian.laplacian f (L y) = 0 :=
    L.continuous.continuousAt.eventually hev
  filter_upwards [hev'] with y hy
  rw [laplacian_comp_linearIsometryEquiv, hy]
  rfl

/-- **The potential of a set outside a disc is harmonic inside the disc** (Section 7, the planar
case of the uniform bound on the local times). In the plane, for a bounded measurable set `E`
outside the disc `B(0,b)`, the potential `U_E` is harmonic at every point of the disc: it is
two times continuously differentiable and its Laplacian vanishes near every point. The proof
writes `U_E` as `2ε/ω₂` times the real part of the holomorphic field `∫_E u_v/(v - z) dv`. -/
theorem harmonicOnNhd_planar_potential (ε : ℝ) {E : Set (EuclideanSpace ℝ (Fin 2))}
    (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) {b : ℝ} (hsub : E ⊆ {v | b ≤ ‖v‖}) :
    InnerProductSpace.HarmonicOnNhd (potential 2 ε E) (Metric.ball 0 b) := by
  intro y hy
  set z : ℂ := mp_e.symm y with hz
  have hzb : ‖z‖ < b := by
    rw [hz, LinearIsometryEquiv.norm_map]
    exact mem_ball_zero_iff.mp hy
  have hF : AnalyticAt ℂ (mp_field E) z :=
    (mp_differentiableOn_field hE hEb hsub).analyticOnNhd Metric.isOpen_ball z
      (mem_ball_zero_iff.mpr hzb)
  have hre : InnerProductSpace.HarmonicAt
      ((2 * ε / unitBallVolume 2) • fun w : ℂ => (mp_field E w).re) z :=
    hF.harmonicAt_re.const_smul
  have hcomp := harmonicAt_comp_linearIsometryEquiv (mp_e.symm : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ)
    (x := y) hre
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr hcomp
  filter_upwards [Metric.isOpen_ball.mem_nhds hy] with y' hy'
  have hz' : ‖mp_e.symm y'‖ < b := by
    rw [LinearIsometryEquiv.norm_map]
    exact mem_ball_zero_iff.mp hy'
  have := mp_potential_eq ε hE hEb hsub hz'
  rw [LinearIsometryEquiv.apply_symm_apply] at this
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
  exact this

/-- **Each coordinate of the planar Newton field is harmonic off the singularity**
(Section 7, the planar case of the uniform bound on the local times). For `v ≠ y` in the plane
and each coordinate `i`, the function `y' ↦ (v - y')_i / |v - y'|²` is harmonic at `y`. -/
theorem harmonicAt_planar_newton_field (v y : EuclideanSpace ℝ (Fin 2)) (hvy : y ≠ v)
    (i : Fin 2) :
    InnerProductSpace.HarmonicAt
      (fun y' : EuclideanSpace ℝ (Fin 2) => (v - y') i / ‖v - y'‖ ^ 2) y := by
  set k : ℂ → ℂ := fun w => (mp_e.symm v - w)⁻¹ with hk
  have hne : mp_e.symm v - mp_e.symm y ≠ 0 := by
    intro h
    apply hvy
    have := sub_eq_zero.mp h
    exact (mp_e.symm.injective this).symm
  have hkan : AnalyticAt ℂ k (mp_e.symm y) :=
    ((analyticAt_const.sub analyticAt_id).inv hne)
  have key : ∀ y' : EuclideanSpace ℝ (Fin 2),
      ((k (mp_e.symm y')).re = (v - y') 0 / ‖v - y'‖ ^ 2) ∧
      (-(k (mp_e.symm y')).im = (v - y') 1 / ‖v - y'‖ ^ 2) := by
    intro y'
    have hw : mp_e.symm v - mp_e.symm y' = mp_e.symm (v - y') := by rw [map_sub]
    have hnorm : Complex.normSq (mp_e.symm (v - y')) = ‖v - y'‖ ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, LinearIsometryEquiv.norm_map]
    have hcoord : ∀ u : EuclideanSpace ℝ (Fin 2),
        (mp_e.symm u).re = u 0 ∧ (mp_e.symm u).im = u 1 := by
      intro u
      constructor <;> simp
    simp only [hk, hw, Complex.inv_re, Complex.inv_im, hnorm, neg_div, neg_neg]
    exact ⟨by rw [(hcoord _).1], by rw [(hcoord _).2]⟩
  fin_cases i
  · have hh := harmonicAt_comp_linearIsometryEquiv
      (mp_e.symm : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ) (x := y) hkan.harmonicAt_re
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hh
    exact Filter.Eventually.of_forall fun y' => by simpa using (key y').1
  · have hh := harmonicAt_comp_linearIsometryEquiv
      (mp_e.symm : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ) (x := y) hkan.harmonicAt_im.neg
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hh
    exact Filter.Eventually.of_forall fun y' => by simpa using (key y').2


/-- **Consumer of the harmonicity of the planar potential.** The annulus `{1 ≤ |v| ≤ 2}` is a
bounded measurable set of positive area outside the unit disc, and its potential is harmonic at
the origin, an interior point of the disc. -/
theorem harmonicAt_planar_potential_annulus (ε : ℝ) :
    0 < volume {v : EuclideanSpace ℝ (Fin 2) | 1 ≤ ‖v‖ ∧ ‖v‖ ≤ 2} ∧
      InnerProductSpace.HarmonicAt
        (potential 2 ε {v : EuclideanSpace ℝ (Fin 2) | 1 ≤ ‖v‖ ∧ ‖v‖ ≤ 2}) 0 := by
  set A : Set (EuclideanSpace ℝ (Fin 2)) := {v | 1 ≤ ‖v‖ ∧ ‖v‖ ≤ 2} with hA
  have hAm : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hAb : Bornology.IsBounded A := by
    refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin 2))) (r := 2)).subset ?_
    intro v hv
    exact mem_closedBall_zero_iff.mpr hv.2
  have hsub : A ⊆ {v | (1 : ℝ) ≤ ‖v‖} := fun v hv => hv.1
  refine ⟨?_, harmonicOnNhd_planar_potential ε hAm hAb hsub 0
    (mem_ball_zero_iff.mpr (by simp))⟩
  have hc : Metric.ball ((3 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) (1 / 4) ⊆ A := by
    intro v hv
    have h1 : ‖(3 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ = 3 / 2 := by
      simp [norm_smul]
    have h2 := mem_ball_iff_norm.mp hv
    have h3 := norm_sub_norm_le v ((3 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
    have h4 := norm_sub_norm_le ((3 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) v
    rw [h1] at h3 h4
    rw [norm_sub_rev] at h4
    constructor <;> linarith
  exact lt_of_lt_of_le (Metric.measure_ball_pos _ _ (by norm_num)) (measure_mono hc)

/-- **Consumer of the harmonicity of the planar Newton field.** The singularity `v = e₁` is not
the origin, and both coordinates of the Newton field centred at `v` are harmonic at the origin. -/
theorem harmonicAt_planar_newton_field_origin (i : Fin 2) :
    InnerProductSpace.HarmonicAt (fun y' : EuclideanSpace ℝ (Fin 2) =>
      (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) - y') i /
        ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ) - y'‖ ^ 2) 0 := by
  refine harmonicAt_planar_newton_field _ _ ?_ i
  intro h
  have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) h
  simp at this
end CERW.Support.Outer.SourceDisplays
