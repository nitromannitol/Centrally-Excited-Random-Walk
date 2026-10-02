import CERW.Generic.Martingale.LilAssembly.LowerOfSure
import CERW.Generic.Martingale.LilAssembly.ClampPred
import CERW.Generic.Martingale.LilAssembly.Core

/-!
# The reduction of the lower half of the law to the lower bound for padded data

A martingale whose increments are bounded almost surely by a predictable level agrees, almost
surely and at all times, with a martingale whose increments are surely bounded by that level
(`exists_martingale_clamp_pred`). The two have almost surely the same predictable bracket, so the
sure case `lower_of_sure` gives the law for the original martingale.
-/

universe u

namespace CERW.Generic.Martingale.LilAssembly

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.LilLower

/-- Martingales that agree almost surely at all times have almost surely the same predictable
bracket at all times. -/
private theorem predBracket_ae_eq {Ω : Type u} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ m0} {S' S : ℕ → Ω → ℝ} (hae : ∀ᵐ ω ∂μ, ∀ n, S' n ω = S n ω) :
    ∀ᵐ ω ∂μ, ∀ n, CERW.predBracket μ ℱ S' S' n ω = CERW.predBracket μ ℱ S S n ω := by
  have hterm : ∀ t, μ[fun ω => (S' (t + 1) ω - S' t ω) * (S' (t + 1) ω - S' t ω) | ℱ t]
      =ᵐ[μ] μ[fun ω => (S (t + 1) ω - S t ω) * (S (t + 1) ω - S t ω) | ℱ t] := fun t =>
    condExp_congr_ae (hae.mono fun ω hω => by simp only [hω t, hω (t + 1)])
  filter_upwards [ae_all_iff.mpr hterm] with ω hω n
  unfold CERW.predBracket
  rw [Finset.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun t _ => hω t

/-- **The reduction.** -/
theorem reduction_of : Reduction.{u} := by
  intro hNL Ω m0 μ hμ ℱ S hS hLp h0 B hB hBinc hVinf hBratio
  obtain ⟨S', hS', hinc', hS'0, hae⟩ := exists_martingale_clamp_pred hS hB hBinc
  have hbr := predBracket_ae_eq (ℱ := ℱ) hae
  have hsure : SureData μ ℱ S' B :=
    { mart := hS'
      memLp := fun n => (hLp n).ae_eq (hae.mono fun ω hω => (hω n).symm)
      zero := fun ω => (hS'0 ω).trans (h0 ω)
      bPred := hB
      bInc := hinc'
      vInf := by
        filter_upwards [hVinf, hbr] with ω h1 h2
        exact h1.congr fun n => (h2 n).symm
      bRatio := by
        filter_upwards [hBratio, hbr] with ω h1 h2
        refine h1.congr fun n => ?_
        simp only [h2 n] }
  have key := lower_of_sure.{u} hNL μ ℱ hsure
  filter_upwards [key, hae, hbr] with ω hk h1 h2 δ hδ
  exact (hk δ hδ).mono fun n hn => by rwa [h2 n, h1 n] at hn

end CERW.Generic.Martingale.LilAssembly
