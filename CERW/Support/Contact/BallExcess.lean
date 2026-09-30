import CERW.Generic.Kernel.RadialPacking

/-!
# The first moment of a set containing a centred ball

After `eq:quadratic`: if `B(0, b) ⊆ D ⊆ B̄(0, S)`, then
`∫_D |v| dv = (d ω_d/(d + 1)) b^{d+1} + ∫_E |v| dv` with `E = D \ B(0, b)`, and
`0 ≤ ∫_E |v| dv ≤ S |E|`.
-/

namespace CERW.Support.Contact

open MeasureTheory CERW CERW.Generic.Kernel

variable {d : ℕ}

/-- If `B(0, b) ⊆ D ⊆ B̄(0, S)` with `D` measurable, then
`∫_D |v| = d ω_d b^{d+1}/(d + 1) + ∫_{D \ B(0,b)} |v|` and
`0 ≤ ∫_{D \ B(0,b)} |v| ≤ S |D \ B(0,b)|`. -/
theorem integral_norm_eq_ball_add (hd : 1 ≤ d) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) {b S : ℝ} (hb : 0 ≤ b) (hball : Metric.ball 0 b ⊆ D)
    (hDS : D ⊆ Metric.closedBall 0 S) :
    ∫ v in D, ‖v‖ = d * unitBallVolume d * b ^ (d + 1) / (d + 1) +
        ∫ v in D \ Metric.ball 0 b, ‖v‖ ∧
      0 ≤ ∫ v in D \ Metric.ball 0 b, ‖v‖ ∧
      ∫ v in D \ Metric.ball 0 b, ‖v‖ ≤ S * (volume (D \ Metric.ball 0 b)).toReal := by
  have hIntClosed :
      IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (Metric.closedBall 0 S) :=
    ContinuousOn.integrableOn_compact (ProperSpace.isCompact_closedBall 0 S)
      continuous_norm.continuousOn
  have hIntD : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) D :=
    hIntClosed.mono_set hDS
  have hIntB : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (Metric.ball 0 b) :=
    hIntD.mono_set hball
  have hIntE :
      IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (D \ Metric.ball 0 b) :=
    hIntD.mono_set Set.sdiff_subset
  have hEmeas : MeasurableSet (D \ Metric.ball 0 b) := hD.diff measurableSet_ball
  have hfinE : volume (D \ Metric.ball 0 b) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ProperSpace.isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) S).measure_lt_top.ne
      (MeasureTheory.measure_mono (Set.Subset.trans Set.sdiff_subset hDS))
  have hconstInt :
      IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) => S) (D \ Metric.ball 0 b) :=
    MeasureTheory.integrableOn_const hfinE
  refine ⟨?_, ?_, ?_⟩
  · calc ∫ v in D, ‖v‖
        = ∫ v in Metric.ball 0 b ∪ (D \ Metric.ball 0 b), ‖v‖ := by
            rw [Set.union_sdiff_cancel hball]
        _ = (∫ v : EuclideanSpace ℝ (Fin d) in Metric.ball 0 b, ‖v‖)
              + (∫ v in D \ Metric.ball 0 b, ‖v‖) :=
            MeasureTheory.setIntegral_union Set.disjoint_sdiff_right hEmeas hIntB hIntE
        _ = d * unitBallVolume d * b ^ (d + 1) / (d + 1)
              + ∫ v in D \ Metric.ball 0 b, ‖v‖ := by
            rw [integral_ball_norm hd hb]
  · exact MeasureTheory.setIntegral_nonneg hEmeas (fun x _ => norm_nonneg x)
  · have hle : ∀ x ∈ D \ Metric.ball 0 b, ‖x‖ ≤ S :=
      fun x hx => mem_closedBall_zero_iff.mp (hDS hx.1)
    have hmono := MeasureTheory.setIntegral_mono_on hIntE hconstInt hEmeas hle
    rw [MeasureTheory.setIntegral_const, measureReal_def, smul_eq_mul,
      mul_comm (volume (D \ Metric.ball 0 b)).toReal S] at hmono
    exact hmono

end CERW.Support.Contact
