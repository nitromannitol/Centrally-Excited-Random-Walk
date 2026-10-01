import CERW.Model.Martingales
import CERW.Support.LocalTime.KernelAsymptotics

/-!
# The kernel facts for the lattice kernel

The lattice kernel `CERW.latticeKernel d` is the potential kernel `lim_M Σ_{j<M} [P^j(0,0) -
P^j(0,x)]` when `d = 2` and `-G` when `d ≥ 3`. Its kernel facts `KernelFacts` follow from the
two clauses of the kernel asymptotics `eq:kernel-asymptotics`, which the lattice probability
library proves in every dimension (`LatticeProb.External.potentialKernelAsymptotics_holds`),
through `kernelFacts_two` and `kernelFacts_ge_three`. Here the kernel is identified with the
kernel of those asymptotics, so that the facts hold for `latticeKernel d` itself.
-/

namespace CERW.Support.LocalTime

open LatticeProb CERW

/-- The lattice kernel `latticeKernel d` satisfies the kernel facts, with some radial profile
`h`, in every dimension `d ≥ 2`. -/
theorem exists_kernelFacts_latticeKernel {d : ℕ} (hd : 2 ≤ d) :
    ∃ h : ℝ → ℝ, KernelFacts d (latticeKernel d) h := by
  rcases Nat.lt_or_ge d 3 with h3 | h3
  · obtain rfl : d = 2 := by omega
    obtain ⟨b, hlim, κ, C, R, hR, hasymp⟩ :=
      (LatticeProb.External.potentialKernelAsymptotics_holds 2).1 rfl
    have hb : latticeKernel 2 = b := by
      funext x
      simp only [latticeKernel, if_true]
      exact (hlim x).limUnder_eq
    rw [hb]
    exact ⟨_, kernelFacts_two hlim hR hasymp⟩
  · obtain ⟨C, R, hR, hasymp⟩ := (LatticeProb.External.potentialKernelAsymptotics_holds d).2 h3
    have hb : latticeKernel d = fun x => -srwGreenInf d x := by
      funext x
      simp only [latticeKernel]
      rw [if_neg (by omega)]
    rw [hb]
    exact ⟨_, kernelFacts_ge_three h3 hR hasymp⟩

end CERW.Support.LocalTime
