import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The bathtub principle for radial kernels

Among measurable sets of a given finite volume, the ball centred at `y` carries the largest
integral of a nonnegative function of `|v - y|` that is nonincreasing on `(0, ∞)`, and the
centred ball carries the smallest integral of a nonnegative nondecreasing function of `|v|`.
These give the potential bound `eq:potential-bound`, the excess-volume bound `eq:packing`,
and the radial packing inequality `eq:radial-packing`.
-/

namespace CERW.Generic.Kernel

open MeasureTheory

variable {d : ℕ}

/-- Two measurable sets of equal finite volume have set differences of equal volume. -/
theorem measureReal_sdiff_eq_of_measure_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) (hvol : μ s = μ t)
    (hfin : μ t ≠ ⊤) : μ.real (s \ t) = μ.real (t \ s) := by
  have h1 : μ.real (s \ t) + μ.real (s ∩ t) = μ.real s :=
    measureReal_sdiff_add_inter ht (hvol ▸ hfin)
  have h2 : μ.real (t \ s) + μ.real (t ∩ s) = μ.real t := measureReal_sdiff_add_inter hs hfin
  have h3 : μ.real s = μ.real t := by simp only [Measure.real, hvol]
  rw [Set.inter_comm] at h2
  linarith

/-- Bathtub principle: if `D` has the volume of the ball `B(y, ρ)` and `f` is nonnegative and
nonincreasing on `(0, ∞)`, then `∫_D f(|v - y|) ≤ ∫_{B(y,ρ)} f(|v - y|)`, and the left side is
an honest (integrable) integral. -/
theorem setIntegral_le_ball_of_antitoneOn {f : ℝ → ℝ} (hf : AntitoneOn f (Set.Ioi 0))
    (hf0 : ∀ t, 0 < t → 0 ≤ f t) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (y : EuclideanSpace ℝ (Fin d)) {ρ : ℝ} (hρ : 0 < ρ)
    (hvol : volume D = volume (Metric.ball y ρ))
    (hint : IntegrableOn (fun v => f ‖v - y‖) (Metric.ball y ρ)) :
    IntegrableOn (fun v => f ‖v - y‖) D ∧
      ∫ v in D, f ‖v - y‖ ≤ ∫ v in Metric.ball y ρ, f ‖v - y‖ := by
  have hBm : MeasurableSet (Metric.ball y ρ) := Metric.isOpen_ball.measurableSet
  have hBfin : volume (Metric.ball y ρ) ≠ ⊤ := measure_ball_lt_top.ne
  have hDfin : volume D ≠ ⊤ := hvol ▸ hBfin
  have hpos : ∀ t : ℝ, max t ρ ∈ Set.Ioi (0 : ℝ) := fun t => lt_max_of_lt_right hρ
  have hanti : Antitone (fun t : ℝ => f (max t ρ)) :=
    fun a b hab => hf (hpos a) (hpos b) (max_le_max hab le_rfl)
  have hmeas : Measurable (fun v : EuclideanSpace ℝ (Fin d) => f (max ‖v - y‖ ρ)) :=
    hanti.measurable.comp (measurable_norm.comp (measurable_id.sub_const y))
  have hfar : ∀ v ∈ D \ Metric.ball y ρ, f ‖v - y‖ = f (max ‖v - y‖ ρ) := by
    intro v hv
    have hv' : ρ ≤ ‖v - y‖ := by
      have := hv.2
      rwa [mem_ball_iff_norm, not_lt] at this
    rw [max_eq_left hv']
  have hintdiff : IntegrableOn (fun v => f ‖v - y‖) (D \ Metric.ball y ρ) := by
    have hb : IntegrableOn (fun v => f (max ‖v - y‖ ρ)) (D \ Metric.ball y ρ) :=
      Measure.integrableOn_of_bounded (M := f ρ) (measure_ne_top_of_subset Set.sdiff_subset hDfin)
        hmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun v => by
          rw [Real.norm_of_nonneg (hf0 _ (hpos _))]
          exact hf (Set.mem_Ioi.mpr hρ) (hpos _) (le_max_right _ _))
    exact hb.congr_fun (fun v hv => (hfar v hv).symm) (hD.diff hBm)
  have hintD : IntegrableOn (fun v => f ‖v - y‖) D := by
    have := (hint.mono_set (Set.inter_subset_right (s := D))).union hintdiff
    rwa [Set.inter_union_sdiff] at this
  refine ⟨hintD, ?_⟩
  have hsplitD := integral_inter_add_sdiff (μ := volume) hBm hintD
  have hsplitB := integral_inter_add_sdiff (μ := volume) hD hint
  rw [Set.inter_comm] at hsplitB
  have hnear : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      v ∈ Metric.ball y ρ \ D → f ρ ≤ f ‖v - y‖ := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · refine Filter.Eventually.of_forall fun v hv => absurd ?_ hv.2
      obtain ⟨w, hw⟩ := nonempty_of_measure_ne_zero
        (hvol ▸ (Metric.measure_ball_pos volume y hρ).ne')
      rwa [Subsingleton.elim v w]
    · haveI : NeZero d := ⟨hd.ne'⟩
      filter_upwards [Measure.ae_ne volume y] with v hvy hv
      have hv0 : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvy)
      have hv1 : ‖v - y‖ ≤ ρ := (mem_ball_iff_norm.mp hv.1).le
      exact hf hv0 (Set.mem_Ioi.mpr hρ) hv1
  have hle1 : ∫ v in D \ Metric.ball y ρ, f ‖v - y‖ ≤ ∫ _ in D \ Metric.ball y ρ, f ρ :=
    setIntegral_mono_on hintdiff
      (integrableOn_const (measure_ne_top_of_subset Set.sdiff_subset hDfin)) (hD.diff hBm)
      fun v hv => by
        have hv' : ρ ≤ ‖v - y‖ := by
          have := hv.2
          rwa [mem_ball_iff_norm, not_lt] at this
        exact hf (Set.mem_Ioi.mpr hρ) (lt_of_lt_of_le hρ hv') hv'
  have hle2 : ∫ _ in Metric.ball y ρ \ D, f ρ ≤ ∫ v in Metric.ball y ρ \ D, f ‖v - y‖ :=
    setIntegral_mono_on_ae (integrableOn_const (measure_ne_top_of_subset Set.sdiff_subset hBfin))
      (hint.mono_set Set.sdiff_subset) (hBm.diff hD) hnear
  rw [setIntegral_const, smul_eq_mul] at hle1 hle2
  have hreal := measureReal_sdiff_eq_of_measure_eq (μ := volume) hD hBm hvol hBfin
  rw [hreal] at hle1
  linarith

/-- Reverse bathtub principle: if `D` has the volume of the centred ball `B(0, ρ)` and `g` is
nonnegative and nondecreasing on `[0, ∞)`, then `∫_{B(0,ρ)} g(|v|) ≤ ∫_D g(|v|)`. -/
theorem setIntegral_ball_le_of_monotoneOn {g : ℝ → ℝ} (hg : MonotoneOn g (Set.Ici 0))
    (hg0 : ∀ t, 0 ≤ t → 0 ≤ g t) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hvol : volume D = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ))
    (hint : IntegrableOn (fun v => g ‖v‖) D) :
    ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ, g ‖v‖ ≤ ∫ v in D, g ‖v‖ := by
  have hBm : MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ) :=
    Metric.isOpen_ball.measurableSet
  have hBfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hDfin : volume D ≠ ⊤ := hvol ▸ hBfin
  have hpos : ∀ t : ℝ, max t 0 ∈ Set.Ici (0 : ℝ) := fun t => Set.mem_Ici.mpr (le_max_right t 0)
  have hmono : Monotone (fun t : ℝ => g (max t 0)) :=
    fun a b hab => hg (hpos a) (hpos b) (max_le_max hab le_rfl)
  have hmeas : Measurable (fun v : EuclideanSpace ℝ (Fin d) => g (max ‖v‖ 0)) :=
    hmono.measurable.comp measurable_norm
  have hintB : IntegrableOn (fun v => g ‖v‖) (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ) := by
    have hb : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => g (max ‖v‖ 0))
        (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ) :=
      Measure.integrableOn_of_bounded (M := g ρ) hBfin hmeas.aestronglyMeasurable
        (ae_restrict_of_forall_mem hBm fun v hv => by
          rw [Real.norm_of_nonneg (hg0 _ (hpos _))]
          have hv' : ‖v‖ ≤ ρ := (mem_ball_zero_iff.mp hv).le
          rw [max_eq_left (norm_nonneg v)]
          exact hg (Set.mem_Ici.mpr (norm_nonneg v)) (Set.mem_Ici.mpr hρ.le) hv')
    exact hb.congr_fun (fun v _ => by simp only [max_eq_left (norm_nonneg v)]) hBm
  have hsplitD := integral_inter_add_sdiff (μ := volume) hBm hint
  have hsplitB := integral_inter_add_sdiff (μ := volume) hD hintB
  rw [Set.inter_comm] at hsplitB
  have hle1 : ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ \ D, g ‖v‖
      ≤ ∫ _ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ \ D, g ρ :=
    setIntegral_mono_on (hintB.mono_set Set.sdiff_subset)
      (integrableOn_const (measure_ne_top_of_subset Set.sdiff_subset hBfin)) (hBm.diff hD)
      fun v hv => hg (Set.mem_Ici.mpr (norm_nonneg v)) (Set.mem_Ici.mpr hρ.le)
        (mem_ball_zero_iff.mp hv.1).le
  have hle2 : ∫ _ in D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ, g ρ
      ≤ ∫ v in D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ, g ‖v‖ :=
    setIntegral_mono_on (integrableOn_const (measure_ne_top_of_subset Set.sdiff_subset hDfin))
      (hint.mono_set Set.sdiff_subset) (hD.diff hBm)
      fun v hv => by
        have hv' : ρ ≤ ‖v‖ := by
          have := hv.2
          rwa [mem_ball_zero_iff, not_lt] at this
        exact hg (Set.mem_Ici.mpr hρ.le) (Set.mem_Ici.mpr (norm_nonneg v)) hv'
  rw [setIntegral_const, smul_eq_mul] at hle1 hle2
  have hreal := measureReal_sdiff_eq_of_measure_eq (μ := volume) hD hBm hvol hBfin
  rw [hreal] at hle2
  linarith

end CERW.Generic.Kernel
