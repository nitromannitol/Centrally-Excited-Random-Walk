import CERW.Generic.Martingale.LilAssembly.PaddedDataOf
import CERW.Generic.Martingale.LilAssembly.GateOpenAe
import CERW.Generic.Martingale.LilAssembly.AeFst
import CERW.Generic.Martingale.LilAssembly.Core
import CERW.Generic.Martingale.LilLower

/-!
# The lower half of the law for a martingale with sure data

`NiceLower` applied to the padded process of a martingale with sure data, on the product with a
coin space, gives the lower bound for the padded process. On the event that the gate stays open
forever, the padded process and its bracket are the original ones, and that event has probability
one for a large start time.
-/

universe u

namespace CERW.Generic.Martingale.LilAssembly

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.LilLower
open CERW.Generic.Martingale.CLT (pathBracket)

/-- For one `δ` in `(0, 1)`: almost surely `S_n ≥ (1 - δ) ψ(P_n)` infinitely often. -/
theorem lower_fixed (hNL : NiceLower.{u}) {Ω : Type u} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {S B : ℕ → Ω → ℝ}
    (hS : SureData μ ℱ S B) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∀ᵐ ω ∂μ, ∃ᶠ n in atTop,
      (1 - δ) * lilScale (CERW.predBracket μ ℱ S S n ω) ≤ S n ω := by
  obtain ⟨εs, hεs, H⟩ := hNL δ hδ0 hδ1
  obtain ⟨Ξ, mΞ, ν, hν, 𝒦, ε, hε⟩ := exists_signSequence
  haveI := hν
  have hN : ∀ N : ℕ, ∀ᵐ ω ∂μ, (∀ j, padGate μ ℱ S B εs N j ω = 1) →
      ∃ᶠ n in atTop, (1 - δ) * lilScale (pathBracket μ ℱ S n ω) ≤ S n ω := by
    intro N
    have h := H (μ.prod ν) (liftFiltration ℱ 𝒦 hε.mono hε.le) _ _ _ εs N hεs le_rfl
      (paddedData_of μ ν ℱ hε hS εs N)
    refine ae_fst_of_ae_prod μ ν (fun ω => (∀ j, padGate μ ℱ S B εs N j ω = 1) →
      ∃ᶠ n in atTop, (1 - δ) * lilScale (pathBracket μ ℱ S n ω) ≤ S n ω) ?_
    filter_upwards [h] with z hz hG
    have h1 : ∀ n, padProc μ ℱ S B εs N ε n z = S n z.1 :=
      fun n => padded_eq_of_gate _ _ _ n z fun j _ => hG j
    have h2 : ∀ n, padVar μ ℱ S B εs N n z = pathBracket μ ℱ S n z.1 :=
      fun n => paddedBracket_eq_of_gate fun j _ => hG j
    exact hz.mono fun n hn => by rwa [h1 n, h2 n] at hn
  filter_upwards [ae_all_iff.2 hN, gate_open_ae μ ℱ hS hεs,
    ae_all_iff.2 fun k => CERW.Generic.Martingale.CLT.pathBracket_ae_eq_predBracket
      (μ := μ) (ℱ := ℱ) (M := S) k] with ω hω hopen hpath
  obtain ⟨N, hNopen⟩ := hopen
  have h := hω N hNopen
  simp only [hpath] at h
  exact h

/-- **The lower half of the law of the iterated logarithm for a martingale with sure data.** -/
theorem lower_of_sure (hNL : NiceLower.{u}) {Ω : Type u} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {S B : ℕ → Ω → ℝ}
    (hS : SureData μ ℱ S B) :
    ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∃ᶠ n : ℕ in atTop,
      (1 - δ) * Real.sqrt (2 * CERW.predBracket μ ℱ S S n ω *
        Real.log (Real.log (CERW.predBracket μ ℱ S S n ω))) ≤ S n ω := by
  have hpos : ∀ m : ℕ, 0 < 1 / ((m : ℝ) + 2) := fun m => by positivity
  have hlt : ∀ m : ℕ, 1 / ((m : ℝ) + 2) < 1 := fun m => by
    rw [div_lt_one (by positivity)]
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  filter_upwards [ae_all_iff.2 fun m : ℕ => lower_fixed hNL μ ℱ hS (hpos m) (hlt m)]
    with ω hω δ hδ
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  have hle : 1 / ((m : ℝ) + 2) ≤ 1 / ((m : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  refine (hω m).mono fun n hn => le_trans ?_ hn
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

end CERW.Generic.Martingale.LilAssembly
