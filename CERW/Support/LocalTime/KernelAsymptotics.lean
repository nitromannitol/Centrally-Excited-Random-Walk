import LatticeProb.External.PotentialKernelAsymptoticsProved
import CERW.Support.LocalTime.KernelBridge

/-!
# The kernel facts from the lattice kernel asymptotics

The asymptotics `eq:kernel-asymptotics` of the lattice Green function and potential kernel
(Lawler–Limic, Theorems 4.3.1 and 4.4.4) are the proposition
`LatticeProb.External.PotentialKernelAsymptotics d`, which the lattice probability library proves
in every dimension (`LatticeProb.External.potentialKernelAsymptotics_holds`). They provide a
kernel with the facts `KernelFacts` used by every Support proof. In the plane it is the potential
kernel, through `kernelFacts_two`. For `d ≥ 3` it is `-G`, through `kernelFacts_ge_three`.
-/

open LatticeProb (Site)

namespace CERW.Support.LocalTime

/-- The kernel facts from the kernel asymptotics, in every dimension `d ≥ 2`. -/
theorem exists_kernelFacts_of_asymptotics {d : ℕ} (hd : 2 ≤ d)
    (hK : LatticeProb.External.PotentialKernelAsymptotics d) :
    ∃ (b : Site d → ℝ) (h : ℝ → ℝ), KernelFacts d b h := by
  rcases Nat.lt_or_ge d 3 with h3 | h3
  · obtain rfl : d = 2 := by omega
    obtain ⟨b, hlim, κ, C, R, hR, hasymp⟩ := hK.1 rfl
    exact ⟨b, _, kernelFacts_two hlim hR hasymp⟩
  · obtain ⟨C, R, hR, hasymp⟩ := hK.2 h3
    exact ⟨_, _, kernelFacts_ge_three h3 hR hasymp⟩

/-- The kernel facts in every dimension `d ≥ 2`, with no hypothesis: the kernel asymptotics are
proved in the lattice probability library. -/
theorem exists_kernelFacts {d : ℕ} (hd : 2 ≤ d) :
    ∃ (b : Site d → ℝ) (h : ℝ → ℝ), KernelFacts d b h :=
  exists_kernelFacts_of_asymptotics hd (LatticeProb.External.potentialKernelAsymptotics_holds d)

end CERW.Support.LocalTime
