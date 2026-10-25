module

public import CERW.Support.Norm.CoarseVolume
public import CERW.Support.Occupation
public import CERW.LimitShapes.Event

@[expose] public section

/-!
# Geometry at the first exit

The one-step overshoot leaves the occupied cells and contact points strictly inside the
approximation ball used in Proposition `prop:coarse`.
-/

namespace CERW.LimitShapes.Exit

open CERW LatticeProb MeasureTheory
open CERW.Support.Occupation

/-- Before the first exit, the Euclidean radius has at most a one-step overshoot. -/
theorem maxRadius_le_of_first_exit {d : ℕ} (hd : 1 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {R : ℝ} (hR : 0 ≤ R) (X : ℕ → Site d) (n : ℕ) (hX0 : X 0 = 0)
    (hstep : ∀ j, X (j + 1) - X j ∈ unitSteps d)
    (hi : ∀ j, j < n → Ψ (toSpace (X j)) < R) :
    maxRadius X n ≤ R / normMin Ψ + 1 := by
  obtain ⟨hm, hc⟩ := Generic.Norm.normMin_pos_mul_le hΨ hd
  have hj : ∀ j, j < n → euclidNorm (X j) ≤ R / normMin Ψ := by
    intro j hj
    apply (le_div_iff₀ hm).mpr
    have hh := hc (toSpace (X j))
    rw [norm_toSpace] at hh
    nlinarith [hi j hj]
  have hend : euclidNorm (X n) ≤ R / normMin Ψ + 1 := by
    cases n with
    | zero => simpa [hX0, euclidNorm] using
        (show (0 : ℝ) ≤ R / normMin Ψ + 1 by positivity)
    | succ k =>
      have hs := euclidNorm_add_le (X k) (X (k + 1) - X k)
      rw [add_sub_cancel, Support.Law.euclidNorm_of_mem_unitSteps (hstep k)] at hs
      linarith [hj k (Nat.lt_succ_self k)]
  unfold maxRadius
  refine Finset.sup'_le _ _ fun j hjn => ?_
  have hjn' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjn)
  rcases hjn'.lt_or_eq with hjlt | rfl
  · exact (hj j hjlt).trans (by linarith)
  · exact hend

/-- The overshoot and the cell width fit strictly inside the approximation radius. -/
theorem first_exit_radius_lt {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {R : ℝ} (hR : 4 ≤ R) (X : ℕ → Site d) (n : ℕ) (hX0 : X 0 = 0)
    (hstep : ∀ j, X (j + 1) - X j ∈ unitSteps d)
    (hi : ∀ j, j < n → Ψ (toSpace (X j)) < R) :
    maxRadius X n + Real.sqrt d < (1 / normMin Ψ + Real.sqrt d) * R := by
  have hm := maxRadius_le_of_first_exit (by omega) hΨ (by linarith) X n hX0 hstep hi
  have hs : (1 : ℝ) ≤ Real.sqrt d := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr
      (by exact_mod_cast (by omega : 1 ≤ d))
  have hprod : 3 * Real.sqrt d ≤ Real.sqrt d * (R - 1) := by nlinarith
  have heq : (1 / normMin Ψ + Real.sqrt d) * R =
      R / normMin Ψ + Real.sqrt d * R := by ring
  rw [heq]
  linarith

/-- Approximation in an open neighborhood bounds the potential at a contact point. -/
theorem contact_potential_le_of_approximation {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ε : ℝ} (hε : 0 < ε) (X : ℕ → Site d) (n : ℕ) {S δ : ℝ}
    (hD : cellSet X n ⊆ Metric.ball 0 S)
    (ha : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ S →
      |cellLocalTime X n y - normPotential d ε Ψ (cellSet X n) y| ≤ δ)
    {y : EuclideanSpace ℝ (Fin d)} (hcl : y ∈ closure (cellSet X n)ᶜ)
    (hy : ‖y‖ < S) : normPotential d ε Ψ (cellSet X n) y ≤ δ := by
  have hc := Support.Norm.CoarseVolume.continuous_normPotential hd hΨ hε
    Support.Norm.norm_potential_geometry (measurableSet_cellSet X n)
    (Metric.isBounded_ball.subset hD)
  have hb : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S ∩ (cellSet X n)ᶜ,
      normPotential d ε Ψ (cellSet X n) z ≤ δ := by
    rintro z ⟨hz, hzD⟩
    have hh := ha z (mem_ball_zero_iff.mp hz).le
    rw [cellLocalTime_eq_zero_of_not_mem X n hzD, zero_sub, abs_neg] at hh
    exact (le_abs_self _).trans hh
  exact closure_minimal hb (isClosed_le hc continuous_const)
    (Metric.isOpen_ball.inter_closure ⟨mem_ball_zero_iff.mpr hy, hcl⟩)

/-- A uniform positive occupation density in a norm ball gives a time lower bound. -/
theorem time_lower_of_cellLocalTime {d : ℕ}
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (X : ℕ → Site d) (n : ℕ) {r K : ℝ} (hr : 0 < r) (_hK : 0 ≤ K)
    (hsub : {y | Ψ y < r} ⊆ cellSet X n)
    (hl : ∀ y, Ψ y < r → K ≤ cellLocalTime X n y) :
    K * normBallVolume Ψ * r ^ d ≤ (n : ℝ) := by
  have hm : Measurable (cellCenter : EuclideanSpace ℝ (Fin d) → Site d) := by
    rw [measurable_pi_iff]
    intro i
    exact Measurable.floor
      (((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin d → ℝ))).add_const
        (1 / 2))
  have hml : Measurable (cellLocalTime X n) :=
    (measurable_of_countable (fun x : Site d => (localTime X n x : ℝ))).comp hm
  have hDm := measurableSet_cellSet X n
  have hfin : volume (cellSet X n) < ⊤ := by
    rw [volume_cellSet]
    exact ENNReal.natCast_lt_top _
  have hint : IntegrableOn (cellLocalTime X n) (cellSet X n) := by
    refine IntegrableOn.of_bound hfin hml.aestronglyMeasurable.restrict
      (maxLocalTime X n : ℝ) ?_
    filter_upwards with v
    rw [Real.norm_eq_abs, abs_of_nonneg (cellLocalTime_nonneg X n v)]
    change (localTime X n (cellCenter v) : ℝ) ≤ (maxLocalTime X n : ℝ)
    exact_mod_cast localTime_le_maxLocalTime X n (cellCenter v)
  have hB : MeasurableSet {y : EuclideanSpace ℝ (Fin d) | Ψ y < r} :=
    measurableSet_lt (Generic.Norm.norm_continuous hΨ).measurable measurable_const
  have hBF : volume {y : EuclideanSpace ℝ (Fin d) | Ψ y < r} < ⊤ :=
    (measure_mono hsub).trans_lt hfin
  have hle : (∫ _y in {y : EuclideanSpace ℝ (Fin d) | Ψ y < r}, K) ≤ (n : ℝ) := by
    calc
      _ ≤ ∫ y in {y : EuclideanSpace ℝ (Fin d) | Ψ y < r}, cellLocalTime X n y :=
        setIntegral_mono_on (integrableOn_const hBF.ne) (hint.mono_set hsub) hB hl
      _ ≤ ∫ y in cellSet X n, cellLocalTime X n y :=
        setIntegral_mono_set hint (by
          filter_upwards with y using cellLocalTime_nonneg X n y) (Filter.Eventually.of_forall
            (fun y hy => hsub hy))
      _ = n := setIntegral_cellLocalTime X n
  rw [setIntegral_const, smul_eq_mul, measureReal_def,
    Support.Norm.CoarseVolume.volume_sublevel hΨ hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)] at hle
  change K * normBallVolume Ψ * r ^ d ≤ (n : ℝ)
  simpa only [normBallVolume, mul_comm, mul_left_comm, mul_assoc] using hle

end CERW.LimitShapes.Exit
