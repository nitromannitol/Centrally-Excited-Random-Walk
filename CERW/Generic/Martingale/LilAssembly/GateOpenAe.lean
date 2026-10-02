import CERW.Generic.Martingale.LilAssembly.PaddedConstruction

/-!
# The gate is open from some start time on

For a martingale with sure data, the ratio that controls the gate tends to zero almost surely.
So, for any positive level, almost surely there is a start time from which the gate, which is open
before that time, never closes.
-/

namespace CERW.Generic.Martingale.LilAssembly

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.LilLower
open CERW.Generic.Martingale.CLT (pathBracket)

/-- Almost surely there is a start time `N` for which the gate at level `εg` stays open forever. -/
theorem gate_open_ae {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {S B : ℕ → Ω → ℝ} (hS : SureData μ ℱ S B)
    {εg : ℝ} (hεg : 0 < εg) :
    ∀ᵐ ω ∂μ, ∃ N : ℕ, ∀ j, padGate μ ℱ S B εg N j ω = 1 := by
  have hpath : ∀ᵐ ω ∂μ, ∀ k, pathBracket μ ℱ S k ω = CERW.predBracket μ ℱ S S k ω :=
    ae_all_iff.2 fun k => CLT.pathBracket_ae_eq_predBracket μ ℱ S k
  filter_upwards [hS.bRatio, hpath] with ω hω hk
  have hshift := (tendsto_add_atTop_iff_nat 1).2 hω
  have hgate : Tendsto (fun i => gateRatio μ ℱ S B i ω) atTop (𝓝 0) := by
    refine hshift.congr fun i => ?_
    simp only [gateRatio, hk (i + 1)]
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hgate.eventually (ge_mem_nhds hεg))
  exact ⟨N, levelGate_eq_one_of_forall_le _ _ _ hN⟩

end CERW.Generic.Martingale.LilAssembly
