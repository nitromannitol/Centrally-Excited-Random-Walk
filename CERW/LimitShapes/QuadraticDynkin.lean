import CERW.Support.Norm.ContactEvent

/-!
# Martingale property of the quadratic process

The explicit quadratic sum in `sec:norm-event` depends only on the finite past path,
so it is strongly adapted even on exceptional realizations. Almost surely the law gives
unit steps, identifying this sum with the proved Dynkin martingale of the squared norm.
-/

open MeasureTheory LatticeProb
open CERW.Support.Law CERW.Support.Drift
open CERW.Support.Norm.ContactEvent (quadraticMartingale)
open private quadraticMartingale_congr quadraticMartingale_eq_driftDynkin from
  CERW.Support.Norm.ContactEvent

namespace CERW.LimitShapes.QuadraticDynkin

/-- Finite past-path dependence makes the actual quadratic sum strongly adapted,
without any pointwise legality assumption on the paths. -/
theorem stronglyAdapted_quadratic {d : ℕ} {ε : ℝ}
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → Site d}
    (hX : ∀ n, Measurable (X n)) :
    StronglyAdapted (CERW.Support.Law.pathFiltration hX)
      (fun n ω => quadraticMartingale d ε ξ (X · ω) n) := by
  intro n
  have heq : (fun ω => quadraticMartingale d ε ξ (X · ω) n) =
      (fun ω => quadraticMartingale d ε ξ (extendPath (pastPath X n ω)) n) := by
    funext ω
    exact quadraticMartingale_congr fun j hj => (extendPath_pastPath X hj ω).symm
  change StronglyMeasurable[CERW.Support.Law.pathFiltration hX n]
    (fun ω => quadraticMartingale d ε ξ (X · ω) n)
  rw [heq]
  exact stronglyMeasurable_comp_pastPath hX n
    (fun p => quadraticMartingale d ε ξ (extendPath p) n)

/-- The quadratic process of `sec:norm-event` is a martingale: unit steps hold almost
surely by the drift law, and the actual sum is strongly adapted by finite past dependence. -/
theorem martingale_quadratic {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {ξ : LatticeProb.Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) (hξ0 : ξ 0 = 0)
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] {X : ℕ → Ω → LatticeProb.Site d}
    (hX : CERW.IsDriftCERW μ ε ξ X) :
    MeasureTheory.Martingale
      (fun n ω => CERW.Support.Norm.ContactEvent.quadraticMartingale d ε ξ (X · ω) n)
      (CERW.Support.Law.pathFiltration hX.measurable) μ := by
  have hM := martingale_driftDynkin hd hε hξ hX (fun z : Site d => euclidNorm z ^ 2)
  refine hM.congr (stronglyAdapted_quadratic hX.measurable) fun n => ?_
  filter_upwards [ae_all_iff.mpr (ae_sub_mem_unitSteps_drift hd hε hξ hX)] with ω hs
  exact (quadraticMartingale_eq_driftDynkin hd ε ξ hξ0 X ω hs n).symm

end CERW.LimitShapes.QuadraticDynkin
