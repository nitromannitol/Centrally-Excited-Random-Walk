import CERW.LimitShapes.Curvature.PotentialContinuity
import CERW.LimitShapes.Curvature.PotentialHarmonic
import CERW.LimitShapes.Curvature.Decay
import CERW.Generic.Harmonic.Exterior

/-! # Maximum principle for the signed potential

Continuity, harmonicity off the closed band, and decay extend the annular bounds in
`sec:global-profile` to the whole space.
-/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory InnerProductSpace Filter Topology

/-- The annular bound for the actual signed potential extends to the whole space. -/
theorem abs_potential_le_of_annulus {d : ℕ} (hd : 2 ≤ d)
    {ε b R B : ℝ} (hε : 0 < ε) (hb : 0 < b) (hR : b ≤ R) (hB : 0 ≤ B)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hband : ∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ R)
    (hbound : ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ R →
      |CERW.potential d ε E y| ≤ B) :
    ∀ y : EuclideanSpace ℝ (Fin d), |CERW.potential d ε E y| ≤ B := by
  have hd' : 1 ≤ d := by omega
  have hEb : Bornology.IsBounded E :=
    (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin d))) (r := R)).subset
      (fun v hv => by
        simpa only [Metric.mem_closedBall, dist_zero_right] using (hband v hv).2)
  have hbandK : ∀ v ∈ closure E, b ≤ ‖v‖ ∧ ‖v‖ ≤ R := by
    apply closure_minimal (show E ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ R} from hband)
    exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hc := continuous_potential hd hε.le hE hEb
  have hh := harmonicOnNhd_potential (ε := ε) hd hb hR hE hband
  have ht := tendsto_potential_cobounded hd hε.le hb hR hE hband
  have extend (f : EuclideanSpace ℝ (Fin d) → ℝ) (hfc : Continuous f)
      (hfh : HarmonicOnNhd f (closure E)ᶜ)
      (hft : Tendsto f (Bornology.cobounded _) (𝓝 0))
      (hfb : ∀ y, b ≤ ‖y‖ → ‖y‖ ≤ R → f y ≤ B) : ∀ y, f y ≤ B := by
    have hi : HarmonicOnNhd f (Metric.ball 0 b) := by
      intro y hy
      apply hfh y
      intro hyK
      have hyn : ‖y‖ < b := by
        simpa only [Metric.mem_ball, dist_zero_right] using hy
      exact (not_lt_of_ge (hbandK y hyK).1) hyn
    have ho : HarmonicOnNhd f {y | R < ‖y‖} := by
      intro y hy
      apply hfh y
      intro hyK
      exact (not_lt_of_ge (hbandK y hyK).2) hy
    have hib : ∀ y ∈ frontier (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b),
        f y ≤ B := by
      intro y hy
      have heq : ‖y‖ = b := by
        apply frontier_lt_subset_eq continuous_norm continuous_const
        simpa only [Metric.ball, dist_zero_right] using hy
      exact hfb y heq.ge (heq.le.trans hR)
    have hob : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ = R → f y ≤ B := by
      intro y hy
      exact hfb y (hy ▸ hR) hy.le
    intro y
    by_cases hyb : ‖y‖ < b
    · apply Generic.Harmonic.harmonic_le_of_boundary hd' Metric.isOpen_ball
        Metric.isBounded_ball hfc.continuousOn hi hib y
      apply subset_closure
      simpa only [Metric.mem_ball, dist_zero_right] using hyb
    · by_cases hyR : R ≤ ‖y‖
      · exact Generic.Harmonic.harmonic_le_on_exterior hd' (hb.trans_le hR)
          hfc ho hft hB hob y hyR
      · exact hfb y (le_of_not_gt hyb) (le_of_not_ge hyR)
  intro y
  apply abs_le.mpr
  constructor
  · have hn := extend (fun y => -potential d ε E y) hc.neg hh.neg
      (by simpa only [neg_zero] using ht.neg)
      (fun y hyb hyR => by
        simpa only [neg_neg] using neg_le_neg (abs_le.mp (hbound y hyb hyR)).1) y
    linarith
  · exact extend _ hc hh ht (fun y hyb hyR => (abs_le.mp (hbound y hyb hyR)).2) y

end CERW.LimitShapes.Curvature
