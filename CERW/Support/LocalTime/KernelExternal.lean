import CERW.External.LatticePotentialKernel
import CERW.Support.LocalTime.KernelBridge

/-!
# The kernel facts from the cited kernel asymptotics

The External `CERW.External.LatticePotentialKernel d` provides a kernel with the facts
`KernelFacts` used by every Support proof. In the plane it is the potential kernel, through
`kernelFacts_two`. For `d ≥ 3` it is `-G`, through `kernelFacts_ge_three`.
-/

open LatticeProb (Site)

namespace CERW.Support.LocalTime

/-- The kernel facts from the cited kernel asymptotics, in every dimension `d ≥ 2`. -/
theorem exists_kernelFacts {d : ℕ} (hd : 2 ≤ d) (hK : CERW.External.LatticePotentialKernel d) :
    ∃ (b : Site d → ℝ) (h : ℝ → ℝ), KernelFacts d b h := by
  rcases Nat.lt_or_ge d 3 with h3 | h3
  · obtain rfl : d = 2 := by omega
    obtain ⟨b, hlim, κ, C, R, hR, hasymp⟩ := hK.1 rfl
    exact ⟨b, _, kernelFacts_two hlim hR hasymp⟩
  · obtain ⟨C, R, hR, hasymp⟩ := hK.2 h3
    exact ⟨_, _, kernelFacts_ge_three h3 hR hasymp⟩

end CERW.Support.LocalTime
