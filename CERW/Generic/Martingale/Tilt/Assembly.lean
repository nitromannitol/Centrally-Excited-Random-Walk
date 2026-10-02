import CERW.Generic.Martingale.Tilt.Statements

/-!
# The assembly of the sharp lower tail

`TiltTail` at the parameters of `TailArith`.
-/

universe u

namespace CERW.Generic.Martingale.Tilt

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.ExpMart

theorem sharpLowerTail_of (hT : TiltTail.{u}) (hA : TailArith) : SharpLowerTail.{u} := by
  intro η hη
  obtain ⟨ρ₀, ε₀, A₀, θ, hρ₀, _, hε₀, _, hall⟩ := hA η hη
  refine ⟨ρ₀, ε₀, A₀, hρ₀, hε₀, ?_⟩
  intro Ω m0 μ _ ℱ Y b n h v a ρ hv ha hρ hρle hV hA0 hab
  have H := hall v a ρ b hv ha hρ hρle h.nonneg hA0 hab
  obtain ⟨hs, hl, hls, hslb, hsa, hE₁, hE₂, hF⟩ := H
  have key := hT μ ℱ Y b n h (v := v) (ρ := ρ) (s := (a + θ * a) / (v * (1 - ρ)))
    (w := θ * a) (l₁ := θ * a / v) (l₂ := θ * a / v) hs hl hl hls hslb hV
  rw [hsa] at key
  refine hF.trans (le_trans ?_ key)
  exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg _)

end CERW.Generic.Martingale.Tilt
