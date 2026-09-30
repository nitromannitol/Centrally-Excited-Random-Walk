import CERW.Support.Statements
import CERW.Support.LocalTime
import CERW.Support.Main.ScaleLimits
import CERW.Generic.Lattice
import LatticeProb.External.PotentialKernelAsymptoticsProved
import LatticeProb.Walk.HitProb

/-!
# Separated brackets

Lemma 9.3 (`lem:separated-brackets`) of `paper/limit-shapes.tex`, in the probabilistic closure:
assuming the fluctuation rates of Theorem 1.2, with probability at least `1 - C n^{-10}` the
normalized pathwise brackets `⟨S^i, S^j⟩_n` of the martingales attached to the translates
`f_i` of the lattice kernel (a planar dipole of size `k` when `d = 2`) along the first axis have
diagonal entries between two positive constants and off-diagonal entries of order `r_n^{-1/4}`.

The pathwise bracket is decomposed into the local-time weighted sum of the pointwise bracket
`Γ(f, g)` and a first-departure correction (`abs_dynkinBracket_sub_le`). The local time is then
replaced by its profile, using the partial-sum bounds on `Γ` (`bracket_approx`). The totals of
`Γ` come from a summation by parts (`tsum_gammaBr`) and the kernel asymptotics: `2G(y - y')`
for `d ≥ 3` and a logarithmic diagonal for the planar dipole.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Lower

open CERW.Support.Statements

section Helpers

open LatticeProb CERW CERW.Support.Law CERW.Support.LocalTime CERW.Support.Occupation

variable {d : ℕ}

/-- The pointwise covariance `Γ(f, g)(x)` of the nearest-neighbour increments of `f` and `g`
at `x` under simple random walk steps: `(1/2d) Σ_e (f(x+e) - f(x)) (g(x+e) - g(x))
- Δf(x) Δg(x)`, with `Δ = P - I`. -/
private noncomputable def gammaBr (f g : Site d → ℝ) (x : Site d) : ℝ :=
  (1 / (2 * d)) * ∑ e ∈ unitSteps d, (f (x + e) - f x) * (g (x + e) - g x)
    - (walkOp f x - f x) * (walkOp g x - g x)

/-- The walk operator is the average of `u` over the `2d` unit steps. -/
private theorem walkOp_eq_avg (u : Site d → ℝ) (x : Site d) :
    walkOp u x = (1 / (2 * d)) * ∑ e ∈ unitSteps d, u (x + e) := by
  rw [sum_unitSteps, walkOp, nbrSum]
  simp only [sub_eq_add_neg]
  ring

/-- `Δu(x) = (1/2d) Σ_e (u(x + e) - u(x))`. -/
private theorem walkOp_sub_self_eq (hd : 1 ≤ d) (u : Site d → ℝ) (x : Site d) :
    walkOp u x - u x = (1 / (2 * d)) * ∑ e ∈ unitSteps d, (u (x + e) - u x) := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [walkOp_eq_avg, Finset.sum_sub_distrib, Finset.sum_const, card_unitSteps, nsmul_eq_mul]
  push_cast
  field_simp

/-- The pointwise bracket as the covariance of the two increment vectors under uniform
weights. -/
private theorem gammaBr_eq_cov (hd : 1 ≤ d) (f g : Site d → ℝ) (x : Site d) :
    gammaBr f g x = (1 / (2 * d)) * ∑ e ∈ unitSteps d, (f (x + e) - f x) * (g (x + e) - g x)
      - ((1 / (2 * d)) * ∑ e ∈ unitSteps d, (f (x + e) - f x)) *
        ((1 / (2 * d)) * ∑ e ∈ unitSteps d, (g (x + e) - g x)) := by
  rw [gammaBr, walkOp_sub_self_eq hd, walkOp_sub_self_eq hd]

/-- The uniform variance of a vector over the unit steps is nonnegative. -/
private theorem var_nonneg (hd : 1 ≤ d) (c : Site d → ℝ) :
    0 ≤ (1 / (2 * d)) * ∑ e ∈ unitSteps d, c e ^ 2 -
      ((1 / (2 * d)) * ∑ e ∈ unitSteps d, c e) ^ 2 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h := sq_sum_le_card_mul_sum_sq (s := unitSteps d) (f := c)
  rw [card_unitSteps] at h
  push_cast at h
  have hu : (1 / (2 * (d : ℝ))) * (2 * d) = 1 := by field_simp
  have h2 : ((1 / (2 * (d : ℝ))) * ∑ e ∈ unitSteps d, c e) ^ 2 ≤
      (1 / (2 * (d : ℝ))) * ∑ e ∈ unitSteps d, c e ^ 2 := by
    calc ((1 / (2 * (d : ℝ))) * ∑ e ∈ unitSteps d, c e) ^ 2
        = (1 / (2 * (d : ℝ))) ^ 2 * (∑ e ∈ unitSteps d, c e) ^ 2 := by ring
      _ ≤ (1 / (2 * (d : ℝ))) ^ 2 * ((2 * d) * ∑ e ∈ unitSteps d, c e ^ 2) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = (1 / (2 * (d : ℝ))) * ((1 / (2 * d)) * (2 * d)) * ∑ e ∈ unitSteps d, c e ^ 2 := by
          ring
      _ = (1 / (2 * (d : ℝ))) * ∑ e ∈ unitSteps d, c e ^ 2 := by rw [hu]; ring
  linarith

/-- The pointwise bracket of a function with itself is nonnegative. -/
private theorem gammaBr_self_nonneg (hd : 1 ≤ d) (f : Site d → ℝ) (x : Site d) :
    0 ≤ gammaBr f f x := by
  rw [gammaBr_eq_cov hd]
  have := var_nonneg hd (fun e => f (x + e) - f x)
  simp only [sq] at this
  linarith

/-- The pointwise bracket of two functions is at most the mean of the two self brackets. -/
private theorem abs_gammaBr_le (hd : 1 ≤ d) (f g : Site d → ℝ) (x : Site d) :
    |gammaBr f g x| ≤ (gammaBr f f x + gammaBr g g x) / 2 := by
  have hp := var_nonneg hd (fun e => (f (x + e) - f x) + (g (x + e) - g x))
  have hm := var_nonneg hd (fun e => (f (x + e) - f x) - (g (x + e) - g x))
  have e1 : ∑ e ∈ unitSteps d, ((f (x + e) - f x) + (g (x + e) - g x)) ^ 2 =
      ∑ e ∈ unitSteps d, (f (x + e) - f x) * (f (x + e) - f x) +
      2 * ∑ e ∈ unitSteps d, (f (x + e) - f x) * (g (x + e) - g x) +
      ∑ e ∈ unitSteps d, (g (x + e) - g x) * (g (x + e) - g x) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  have e2 : ∑ e ∈ unitSteps d, ((f (x + e) - f x) - (g (x + e) - g x)) ^ 2 =
      ∑ e ∈ unitSteps d, (f (x + e) - f x) * (f (x + e) - f x) -
      2 * ∑ e ∈ unitSteps d, (f (x + e) - f x) * (g (x + e) - g x) +
      ∑ e ∈ unitSteps d, (g (x + e) - g x) * (g (x + e) - g x) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  have s1 : ∑ e ∈ unitSteps d, ((f (x + e) - f x) + (g (x + e) - g x)) =
      ∑ e ∈ unitSteps d, (f (x + e) - f x) + ∑ e ∈ unitSteps d, (g (x + e) - g x) :=
    Finset.sum_add_distrib
  have s2 : ∑ e ∈ unitSteps d, ((f (x + e) - f x) - (g (x + e) - g x)) =
      ∑ e ∈ unitSteps d, (f (x + e) - f x) - ∑ e ∈ unitSteps d, (g (x + e) - g x) := by
    rw [Finset.sum_sub_distrib]
  rw [e1, s1] at hp
  rw [e2, s2] at hm
  rw [gammaBr_eq_cov hd f g, gammaBr_eq_cov hd f f, gammaBr_eq_cov hd g g]
  rw [abs_le]
  constructor <;> nlinarith [hp, hm]


/-! ### Shared kernel facts -/

/-- The lattice kernel satisfies the kernel facts. -/
private theorem exists_kernelFacts_lattice (hd : 2 ≤ d) :
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

/-- The one-step bound for the lattice kernel. -/
private theorem kernel_grad (hd : 2 ≤ d) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ x : Site d, ∀ e ∈ unitSteps d,
      |latticeKernel d (x + e) - latticeKernel d x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)) := by
  obtain ⟨h, hK⟩ := exists_kernelFacts_lattice (d := d) hd
  obtain ⟨Cg, hgrad⟩ := hK.gradBound
  refine ⟨|Cg|, abs_nonneg _, fun x e he => (hgrad x e he).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_abs_self _)
    (Real.rpow_nonneg (by linarith [euclidNorm_nonneg x]) _)

/-- The Poisson equation `(P - I) b = 1_{0}` for the lattice kernel. -/
private theorem kernel_poisson (hd : 2 ≤ d) (x : Site d) :
    walkOp (latticeKernel d) x - latticeKernel d x = if x = 0 then 1 else 0 := by
  obtain ⟨h, hK⟩ := exists_kernelFacts_lattice (d := d) hd
  exact hK.poisson x

/-- The planar lattice kernel is `(2/π) log |x| + κ + O(|x|^{-2})`. -/
private theorem kernel_asymp_two :
    ∃ κ C R : ℝ, 1 ≤ R ∧ ∀ x : Site 2, R ≤ euclidNorm x →
      |latticeKernel 2 x - (2 / Real.pi * Real.log (euclidNorm x) + κ)| ≤
        C * euclidNorm x ^ (-2 : ℝ) := by
  obtain ⟨b, hlim, κ, C, R, hR, hasymp⟩ :=
    (LatticeProb.External.potentialKernelAsymptotics_holds 2).1 rfl
  have hb : latticeKernel 2 = b := by
    funext x
    simp only [latticeKernel, if_true]
    exact (hlim x).limUnder_eq
  exact ⟨κ, C, R, hR, by rw [hb]; exact hasymp⟩

/-- Translating a real power: `(1 + |x - y|)^p ≤ (1 + |y|)^{-p} (1 + |x|)^p` for `p ≤ 0`. -/
private theorem rpow_translate {p : ℝ} (hp : p ≤ 0) (y x : Site d) :
    (1 + euclidNorm (x - y)) ^ p ≤ (1 + euclidNorm y) ^ (-p) * (1 + euclidNorm x) ^ p := by
  have h1 : 1 + euclidNorm x ≤ (1 + euclidNorm y) * (1 + euclidNorm (x - y)) := by
    have h := euclidNorm_add_le (x - y) y
    rw [sub_add_cancel] at h
    nlinarith [euclidNorm_nonneg x, euclidNorm_nonneg y, euclidNorm_nonneg (x - y)]
  have hy : 0 < 1 + euclidNorm y := by linarith [euclidNorm_nonneg y]
  have hxy : 0 < 1 + euclidNorm (x - y) := by linarith [euclidNorm_nonneg (x - y)]
  have hx : 0 < 1 + euclidNorm x := by linarith [euclidNorm_nonneg x]
  have h2 : (1 + euclidNorm x) / (1 + euclidNorm y) ≤ 1 + euclidNorm (x - y) := by
    rw [div_le_iff₀ hy]
    linarith [h1]
  calc (1 + euclidNorm (x - y)) ^ p ≤ ((1 + euclidNorm x) / (1 + euclidNorm y)) ^ p :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h2 hp
    _ = (1 + euclidNorm y) ^ (-p) * (1 + euclidNorm x) ^ p := by
        rw [Real.div_rpow hx.le hy.le, Real.rpow_neg hy.le, div_eq_mul_inv, mul_comm]

/-- The translate `x ↦ b(x - y)` of the lattice kernel has Laplacian `1_{y}`. -/
private theorem kernel_translate_lap (hd : 2 ≤ d) (y x : Site d) :
    walkOp (fun z => latticeKernel d (z - y)) x - latticeKernel d (x - y) =
      if x = y then 1 else 0 := by
  have h := kernel_poisson hd (x - y)
  have hw : walkOp (fun z => latticeKernel d (z - y)) x = walkOp (latticeKernel d) (x - y) := by
    rw [walkOp_eq_avg, walkOp_eq_avg]
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [add_sub_right_comm]
  rw [hw, h]
  simp only [sub_eq_zero]

/-! ### Summation of the bracket and the kernel sums -/

/-- `f = O((1+|x|)^{-α})`, with one-step differences `O((1+|x|)^{-β})`. -/
private def Decays (d : ℕ) (α β : ℝ) (f : Site d → ℝ) : Prop :=
  ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
    (∀ x, ∀ e ∈ unitSteps d, |f (x + e) - f x| ≤ C₁ * (1 + euclidNorm x) ^ (-β)) ∧
    ∀ x, |f x| ≤ C₂ * (1 + euclidNorm x) ^ (-α)


/-- A unit step is nonzero. -/
private theorem sbp_unitStep_ne_zero {e : Site d} (he : e ∈ unitSteps d) :
    e ≠ 0 := by
  obtain ⟨i, rfl | rfl⟩ := mem_unitSteps.mp he
  · exact unit_ne_zero i
  · exact neg_ne_zero.mpr (unit_ne_zero i)

/-- The negative of a unit step is a unit step. -/
private theorem sbp_neg_mem {e : Site d} (he : e ∈ unitSteps d) :
    -e ∈ unitSteps d := by
  obtain ⟨i, rfl | rfl⟩ := mem_unitSteps.mp he
  · exact mem_unitSteps.mpr ⟨i, Or.inr rfl⟩
  · exact mem_unitSteps.mpr ⟨i, Or.inl (neg_neg _)⟩

/-- Every coordinate of a unit step has modulus at most one. -/
private theorem sbp_abs_coord_le {e : Site d} (he : e ∈ unitSteps d) (i : Fin d) :
    |e i| ≤ 1 := by
  obtain ⟨j, rfl | rfl⟩ := mem_unitSteps.mp he
  · simp only [unit, Pi.single_apply]
    split_ifs <;> simp
  · simp only [unit, Pi.neg_apply, Pi.single_apply]
    split_ifs <;> simp

/-- A unit step moves a point of the box of radius `n` into the box of radius `n + 1`. -/
private theorem sbp_add_mem_box {n : ℕ} {x e : Site d}
    (hx : x ∈ boxFinset (0 : Site d) n) (he : e ∈ unitSteps d) :
    x + e ∈ boxFinset (0 : Site d) (n + 1) := by
  rw [mem_boxFinset_zero_iff] at hx ⊢
  rw [supNorm_le_iff] at hx ⊢
  intro i
  have h1 := hx i
  have h2 := sbp_abs_coord_le he i
  rw [Pi.add_apply]
  calc |x i + e i| ≤ |x i| + |e i| := abs_add_le _ _
    _ ≤ (n : ℤ) + 1 := add_le_add h1 h2
    _ = ((n + 1 : ℕ) : ℤ) := by push_cast; ring

/-- The sum of `Δφ` over a finite set is the boundary flux
`(1/2d) Σ_{x ∈ B, e, x + e ∉ B} (φ(x + e) - φ(x))`. -/
private theorem sbp_sum_laplace (hd : 1 ≤ d) (B : Finset (Site d))
    (φ : Site d → ℝ) :
    ∑ x ∈ B, (walkOp φ x - φ x) =
      (1 / (2 * d)) * ∑ p ∈ (B ×ˢ unitSteps d).filter (fun p => p.1 + p.2 ∉ B),
        (φ (p.1 + p.2) - φ p.1) := by
  have h1 : ∑ x ∈ B, (walkOp φ x - φ x) =
      (1 / (2 * d)) * ∑ p ∈ B ×ˢ unitSteps d, (φ (p.1 + p.2) - φ p.1) := by
    rw [Finset.sum_product, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => walkOp_sub_self_eq hd φ x
  rw [h1]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not (B ×ˢ unitSteps d) (fun p => p.1 + p.2 ∈ B)]
  have h0 : ∑ p ∈ (B ×ˢ unitSteps d).filter (fun p => p.1 + p.2 ∈ B),
      (φ (p.1 + p.2) - φ p.1) = 0 := by
    refine Finset.sum_involution (fun p _ => (p.1 + p.2, -p.2)) ?_ ?_ ?_ ?_
    · intro p _
      simp only [add_neg_cancel_right]
      ring
    · intro p hp _ h
      have hp' := Finset.mem_filter.mp hp
      have he := (Finset.mem_product.mp hp'.1).2
      have h2 : p.1 + p.2 = p.1 := congrArg Prod.fst h
      exact sbp_unitStep_ne_zero he (by simpa using h2)
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hx := (Finset.mem_product.mp hp'.1).1
      have he := (Finset.mem_product.mp hp'.1).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp'.2, ?_⟩, ?_⟩
      · exact sbp_neg_mem he
      · simpa using hx
    · intro p _
      simp
  rw [h0, zero_add]

/-- The boundary pairs of the box of radius `n + 1` have first coordinate in the outer shell. -/
private theorem sbp_bdry_subset (n : ℕ) :
    (boxFinset (0 : Site d) (n + 1) ×ˢ unitSteps d).filter
        (fun p => p.1 + p.2 ∉ boxFinset (0 : Site d) (n + 1)) ⊆
      (boxFinset (0 : Site d) (n + 1) \ boxFinset (0 : Site d) n) ×ˢ unitSteps d := by
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
  obtain ⟨hx, he⟩ := Finset.mem_product.mp hp1
  refine Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨hx, fun hn => hp2 ?_⟩, he⟩
  exact sbp_add_mem_box hn he

/-- The bracket is `Γ(f, g) = Δ(f g) - (g Δf + f Δg + Δf Δg)`. -/
private theorem sbp_gammaBr_eq (hd : 1 ≤ d) (f g : Site d → ℝ) (x : Site d) :
    gammaBr f g x = (walkOp (fun z => f z * g z) x - f x * g x) -
      (g x * (walkOp f x - f x) + f x * (walkOp g x - g x) +
        (walkOp f x - f x) * (walkOp g x - g x)) := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : ∑ e ∈ unitSteps d, (f (x + e) - f x) * (g (x + e) - g x) =
      ∑ e ∈ unitSteps d, f (x + e) * g (x + e) - g x * ∑ e ∈ unitSteps d, f (x + e)
        - f x * ∑ e ∈ unitSteps d, g (x + e) + 2 * d * (f x * g x) := by
    have h2 : ∀ e ∈ unitSteps d, (f (x + e) - f x) * (g (x + e) - g x) =
        f (x + e) * g (x + e) - g x * f (x + e) - f x * g (x + e) + f x * g x :=
      fun e _ => by ring
    rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
      card_unitSteps, nsmul_eq_mul]
    push_cast
    ring
  rw [gammaBr, h1, walkOp_eq_avg (fun z => f z * g z), walkOp_eq_avg f, walkOp_eq_avg g]
  field_simp
  ring

/-- The one-step differences of a product of decaying functions are `O((1 + |x|)^{-d})`. -/
private theorem sbp_prod_grad {α β : ℝ} (hαβ : α ≤ β) (hdαβ : (d : ℝ) ≤ α + β)
    {f g : Site d → ℝ} {C₁ C₂ D₁ D₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hD₁ : 0 ≤ D₁)
    (hD₂ : 0 ≤ D₂)
    (hf1 : ∀ x, ∀ e ∈ unitSteps d, |f (x + e) - f x| ≤ C₁ * (1 + euclidNorm x) ^ (-β))
    (hf2 : ∀ x, |f x| ≤ C₂ * (1 + euclidNorm x) ^ (-α))
    (hg1 : ∀ x, ∀ e ∈ unitSteps d, |g (x + e) - g x| ≤ D₁ * (1 + euclidNorm x) ^ (-β))
    (hg2 : ∀ x, |g x| ≤ D₂ * (1 + euclidNorm x) ^ (-α)) (x : Site d) {e : Site d}
    (he : e ∈ unitSteps d) :
    |f (x + e) * g (x + e) - f x * g x| ≤
      (C₁ * D₂ + C₂ * D₁ + C₁ * D₁) * (1 + euclidNorm x) ^ (-(d : ℝ)) := by
  set t : ℝ := 1 + euclidNorm x with ht
  have ht1 : 1 ≤ t := by linarith [euclidNorm_nonneg x]
  have ht0 : 0 < t := by linarith
  have hab : t ^ (-β) * t ^ (-α) ≤ t ^ (-(d : ℝ)) := by
    rw [← Real.rpow_add ht0]
    exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  have hba : t ^ (-α) * t ^ (-β) ≤ t ^ (-(d : ℝ)) := by rw [mul_comm]; exact hab
  have hbb : t ^ (-β) * t ^ (-β) ≤ t ^ (-(d : ℝ)) := by
    rw [← Real.rpow_add ht0]
    exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  have hid' : f (x + e) * g (x + e) - f x * g x =
      (f (x + e) - f x) * g x + f x * (g (x + e) - g x) +
        (f (x + e) - f x) * (g (x + e) - g x) := by ring
  rw [hid']
  have p1 : |(f (x + e) - f x) * g x| ≤ C₁ * D₂ * t ^ (-(d : ℝ)) := by
    rw [abs_mul]
    calc |f (x + e) - f x| * |g x| ≤ (C₁ * t ^ (-β)) * (D₂ * t ^ (-α)) :=
          mul_le_mul (hf1 x e he) (hg2 x) (abs_nonneg _) (by positivity)
      _ = C₁ * D₂ * (t ^ (-β) * t ^ (-α)) := by ring
      _ ≤ C₁ * D₂ * t ^ (-(d : ℝ)) := mul_le_mul_of_nonneg_left hab (by positivity)
  have p2 : |f x * (g (x + e) - g x)| ≤ C₂ * D₁ * t ^ (-(d : ℝ)) := by
    rw [abs_mul]
    calc |f x| * |g (x + e) - g x| ≤ (C₂ * t ^ (-α)) * (D₁ * t ^ (-β)) :=
          mul_le_mul (hf2 x) (hg1 x e he) (abs_nonneg _) (by positivity)
      _ = C₂ * D₁ * (t ^ (-α) * t ^ (-β)) := by ring
      _ ≤ C₂ * D₁ * t ^ (-(d : ℝ)) := mul_le_mul_of_nonneg_left hba (by positivity)
  have p3 : |(f (x + e) - f x) * (g (x + e) - g x)| ≤ C₁ * D₁ * t ^ (-(d : ℝ)) := by
    rw [abs_mul]
    calc |f (x + e) - f x| * |g (x + e) - g x| ≤ (C₁ * t ^ (-β)) * (D₁ * t ^ (-β)) :=
          mul_le_mul (hf1 x e he) (hg1 x e he) (abs_nonneg _) (by positivity)
      _ = C₁ * D₁ * (t ^ (-β) * t ^ (-β)) := by ring
      _ ≤ C₁ * D₁ * t ^ (-(d : ℝ)) := mul_le_mul_of_nonneg_left hbb (by positivity)
  calc |(f (x + e) - f x) * g x + f x * (g (x + e) - g x) +
        (f (x + e) - f x) * (g (x + e) - g x)|
      ≤ |(f (x + e) - f x) * g x| + |f x * (g (x + e) - g x)| +
        |(f (x + e) - f x) * (g (x + e) - g x)| := abs_add_three _ _ _
    _ ≤ C₁ * D₂ * t ^ (-(d : ℝ)) + C₂ * D₁ * t ^ (-(d : ℝ)) + C₁ * D₁ * t ^ (-(d : ℝ)) :=
        add_le_add (add_le_add p1 p2) p3
    _ = (C₁ * D₂ + C₂ * D₁ + C₁ * D₁) * t ^ (-(d : ℝ)) := by ring

/-- The flux of `Δφ` through the box of radius `n + 1` is `O(1/n)` when `φ` has one-step
differences `O((1 + |x|)^{-d})`. -/
private theorem sbp_flux_bound (hd : 2 ≤ d) {φ : Site d → ℝ} {Cφ : ℝ} (hCφ : 0 ≤ Cφ)
    (hφ : ∀ x, ∀ e ∈ unitSteps d,
      |φ (x + e) - φ x| ≤ Cφ * (1 + euclidNorm x) ^ (-(d : ℝ))) (n : ℕ) :
    |∑ x ∈ boxFinset (0 : Site d) (n + 1), (walkOp φ x - φ x)| ≤
      2 * d * 2 ^ (d - 1) * Cφ / ((n : ℝ) + 2) := by
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  set B := boxFinset (0 : Site d) (n + 1) with hB
  set bd := (B ×ˢ unitSteps d).filter (fun p => p.1 + p.2 ∉ B) with hbd
  have hbound : ∀ p ∈ bd, |φ (p.1 + p.2) - φ p.1| ≤
      Cφ * ((n : ℝ) + 2) ^ (-(d : ℝ)) := by
    intro p hp
    have hsub := sbp_bdry_subset (d := d) n hp
    obtain ⟨hx, he⟩ := Finset.mem_product.mp hsub
    have hsn : supNorm p.1 = n + 1 := supNorm_eq_of_mem_sdiff hx
    have hnorm : ((n : ℝ) + 1) ≤ euclidNorm p.1 := by
      have := supNorm_le_euclidNorm p.1
      rw [hsn] at this
      push_cast at this
      exact this
    have h1 := hφ p.1 p.2 he
    have h2 : (1 + euclidNorm p.1) ^ (-(d : ℝ)) ≤ ((n : ℝ) + 2) ^ (-(d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hn2 (by linarith) (by linarith)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hCφ)
  have hcard : (bd.card : ℝ) ≤ (shellCard d (n + 1) : ℝ) * (2 * d) := by
    have h1 := Finset.card_le_card (sbp_bdry_subset (d := d) n)
    rw [Finset.card_product, card_sdiff_box, card_unitSteps] at h1
    have h2 : (bd.card : ℝ) ≤ ((shellCard d (n + 1) * (2 * d) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact h2
  have hshell : (shellCard d (n + 1) : ℝ) ≤ 2 * d * 2 ^ (d - 1) * ((n : ℝ) + 2) ^ (d - 1) := by
    have h1 := shellCard_le d (k := n + 1) (by omega)
    push_cast at h1
    refine h1.trans ?_
    have h3 : (2 * ((n : ℝ) + 1) + 1) ^ (d - 1) ≤ (2 * ((n : ℝ) + 2)) ^ (d - 1) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    rw [mul_pow] at h3
    calc 2 * (d : ℝ) * (2 * ((n : ℝ) + 1) + 1) ^ (d - 1)
        ≤ 2 * d * (2 ^ (d - 1) * ((n : ℝ) + 2) ^ (d - 1)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 * d * 2 ^ (d - 1) * ((n : ℝ) + 2) ^ (d - 1) := by ring
  have hpow : ((n : ℝ) + 2) ^ (d - 1) * ((n : ℝ) + 2) ^ (-(d : ℝ)) = 1 / ((n : ℝ) + 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn2, one_div, ← Real.rpow_neg_one]
    congr 1
    rw [Nat.cast_sub hd1]
    push_cast
    ring
  rw [sbp_sum_laplace hd1, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * d))]
  have hsum : |∑ p ∈ bd, (φ (p.1 + p.2) - φ p.1)| ≤
      bd.card * (Cφ * ((n : ℝ) + 2) ^ (-(d : ℝ))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ p ∈ bd, |φ (p.1 + p.2) - φ p.1|
        ≤ ∑ _p ∈ bd, Cφ * ((n : ℝ) + 2) ^ (-(d : ℝ)) := Finset.sum_le_sum hbound
      _ = bd.card * (Cφ * ((n : ℝ) + 2) ^ (-(d : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hW : 0 ≤ Cφ * ((n : ℝ) + 2) ^ (-(d : ℝ)) :=
    mul_nonneg hCφ (Real.rpow_nonneg hn2.le _)
  calc (1 / (2 * d : ℝ)) * |∑ p ∈ bd, (φ (p.1 + p.2) - φ p.1)|
      ≤ (1 / (2 * d : ℝ)) * (bd.card * (Cφ * ((n : ℝ) + 2) ^ (-(d : ℝ)))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (1 / (2 * d : ℝ)) * ((shellCard d (n + 1) : ℝ) * (2 * d) *
          (Cφ * ((n : ℝ) + 2) ^ (-(d : ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hW) (by positivity)
    _ = (shellCard d (n + 1) : ℝ) * (Cφ * ((n : ℝ) + 2) ^ (-(d : ℝ))) := by
        field_simp
    _ ≤ (2 * d * 2 ^ (d - 1) * ((n : ℝ) + 2) ^ (d - 1)) *
          (Cφ * ((n : ℝ) + 2) ^ (-(d : ℝ))) := mul_le_mul_of_nonneg_right hshell hW
    _ = 2 * d * 2 ^ (d - 1) * Cφ * (((n : ℝ) + 2) ^ (d - 1) *
          ((n : ℝ) + 2) ^ (-(d : ℝ))) := by ring
    _ = 2 * d * 2 ^ (d - 1) * Cφ / ((n : ℝ) + 2) := by rw [hpow]; ring

/-- Box sums of the bracket: for decaying `f`, `g` with Laplacians supported in `T`, the sum of
`Γ(f, g)` over a box of radius `n + 1` containing `T` is minus the total
`Σ_T (g Δf + f Δg + Δf Δg)`, up to a flux of order `1/n`. -/
private theorem sbp_box_sum (hd : 2 ≤ d) {α β : ℝ} (hαβ : α ≤ β) (hdαβ : (d : ℝ) ≤ α + β)
    {f g : Site d → ℝ} (hf : Decays d α β f) (hg : Decays d α β g) (T : Finset (Site d))
    (hTf : ∀ x ∉ T, walkOp f x - f x = 0) (hTg : ∀ x ∉ T, walkOp g x - g x = 0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n : ℕ, T ⊆ boxFinset (0 : Site d) (n + 1) →
      |∑ x ∈ boxFinset (0 : Site d) (n + 1), gammaBr f g x +
        ∑ x ∈ T, (g x * (walkOp f x - f x) + f x * (walkOp g x - g x) +
          (walkOp f x - f x) * (walkOp g x - g x))| ≤ c / ((n : ℝ) + 2) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₁, C₂, hC₁, hC₂, hf1, hf2⟩ := hf
  obtain ⟨D₁, D₂, hD₁, hD₂, hg1, hg2⟩ := hg
  have hCφ : 0 ≤ C₁ * D₂ + C₂ * D₁ + C₁ * D₁ := by positivity
  have hφ : ∀ x, ∀ e ∈ unitSteps d,
      |(fun z => f z * g z) (x + e) - (fun z => f z * g z) x| ≤
        (C₁ * D₂ + C₂ * D₁ + C₁ * D₁) * (1 + euclidNorm x) ^ (-(d : ℝ)) :=
    fun x e he => sbp_prod_grad hαβ hdαβ hC₁ hC₂ hD₁ hD₂ hf1 hf2 hg1 hg2 x he
  refine ⟨2 * d * 2 ^ (d - 1) * (C₁ * D₂ + C₂ * D₁ + C₁ * D₁), by positivity, fun n hn => ?_⟩
  set h : Site d → ℝ := fun x => g x * (walkOp f x - f x) + f x * (walkOp g x - g x) +
    (walkOp f x - f x) * (walkOp g x - g x) with hh
  have hvanish : ∀ x ∉ T, h x = 0 := by
    intro x hx
    simp only [hh, hTf x hx, hTg x hx]
    ring
  have hbox : ∑ x ∈ boxFinset (0 : Site d) (n + 1), h x = ∑ x ∈ T, h x :=
    (Finset.sum_subset hn fun x _ hxT => hvanish x hxT).symm
  have hsum1 : ∑ x ∈ boxFinset (0 : Site d) (n + 1), gammaBr f g x =
      ∑ x ∈ boxFinset (0 : Site d) (n + 1),
        (walkOp (fun z => f z * g z) x - (fun z => f z * g z) x) -
        ∑ x ∈ boxFinset (0 : Site d) (n + 1), h x := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => sbp_gammaBr_eq hd1 f g x
  rw [hsum1, hbox]
  have := sbp_flux_bound (φ := fun z => f z * g z) hd hCφ hφ n
  convert this using 2
  ring

/-- The bracket of a decaying function with itself is summable. -/
private theorem sbp_summable_self (hd : 2 ≤ d) {α β : ℝ} (hαβ : α ≤ β)
    (hdαβ : (d : ℝ) ≤ α + β) {f : Site d → ℝ} (hf : Decays d α β f) (T : Finset (Site d))
    (hT : ∀ x ∉ T, walkOp f x - f x = 0) : Summable (gammaBr f f) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c, hc, hbox⟩ := sbp_box_sum hd hαβ hdαβ hf hf T hT hT
  set V : ℝ := ∑ x ∈ T, (f x * (walkOp f x - f x) + f x * (walkOp f x - f x) +
    (walkOp f x - f x) * (walkOp f x - f x)) with hV
  refine summable_of_sum_le (c := c + |V|) (fun x => gammaBr_self_nonneg hd1 f x) fun u => ?_
  set N : ℕ := T.sup supNorm + u.sup supNorm with hN
  have hTsub : T ⊆ boxFinset (0 : Site d) (N + 1) := fun x hx => by
    rw [mem_boxFinset_zero_iff]
    have := Finset.le_sup (f := supNorm) hx
    omega
  have husub : u ⊆ boxFinset (0 : Site d) (N + 1) := fun x hx => by
    rw [mem_boxFinset_zero_iff]
    have := Finset.le_sup (f := supNorm) hx
    omega
  have h1 := hbox N hTsub
  have h2 : c / ((N : ℝ) + 2) ≤ c := div_le_self hc (by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith)
  calc ∑ x ∈ u, gammaBr f f x
      ≤ ∑ x ∈ boxFinset (0 : Site d) (N + 1), gammaBr f f x :=
        Finset.sum_le_sum_of_subset_of_nonneg husub fun x _ _ => gammaBr_self_nonneg hd1 f x
    _ ≤ c + |V| := by
        have h3 := (abs_le.mp h1).2
        have h4 := neg_le_abs V
        linarith

/-- **Summation of the bracket**: for decaying `f`, `g` whose Laplacians are supported in a
finite set `T`, the bracket `Γ(f, g)` is summable, with total
`-Σ_T (g Δf + f Δg + Δf Δg)`. -/
private theorem tsum_gammaBr (hd : 2 ≤ d) {α β : ℝ} (hαβ : α ≤ β)
    (hdαβ : (d : ℝ) ≤ α + β) {f g : Site d → ℝ} (hf : Decays d α β f) (hg : Decays d α β g)
    (T : Finset (Site d)) (hTf : ∀ x ∉ T, walkOp f x - f x = 0)
    (hTg : ∀ x ∉ T, walkOp g x - g x = 0) :
    Summable (gammaBr f g) ∧
      ∑' x, gammaBr f g x = -∑ x ∈ T, (g x * (walkOp f x - f x) + f x * (walkOp g x - g x) +
        (walkOp f x - f x) * (walkOp g x - g x)) := by
  have hd1 : 1 ≤ d := by omega
  have hsf := sbp_summable_self hd hαβ hdαβ hf T hTf
  have hsg := sbp_summable_self hd hαβ hdαβ hg T hTg
  have hsfg : Summable (gammaBr f g) := by
    refine Summable.of_norm_bounded ((hsf.add hsg).div_const 2) fun x => ?_
    rw [Real.norm_eq_abs]
    exact abs_gammaBr_le hd1 f g x
  refine ⟨hsfg, ?_⟩
  obtain ⟨c, hc, hbox⟩ := sbp_box_sum hd hαβ hdαβ hf hg T hTf hTg
  set V : ℝ := ∑ x ∈ T, (g x * (walkOp f x - f x) + f x * (walkOp g x - g x) +
    (walkOp f x - f x) * (walkOp g x - g x)) with hV
  set N₀ : ℕ := T.sup supNorm with hN₀
  have hTsub : ∀ n : ℕ, N₀ ≤ n + 1 → T ⊆ boxFinset (0 : Site d) (n + 1) := by
    intro n hn x hx
    rw [mem_boxFinset_zero_iff]
    exact (Finset.le_sup (f := supNorm) hx).trans hn
  have hexh : Tendsto (fun n : ℕ => boxFinset (0 : Site d) (n + 1)) atTop atTop := by
    refine tendsto_atTop_finset_of_monotone (fun m n hmn => ?_) fun x => ⟨supNorm x, ?_⟩
    · exact boxFinset_zero_subset (by omega)
    · rw [mem_boxFinset_zero_iff]
      omega
  have hlim1 : Tendsto (fun n : ℕ => ∑ x ∈ boxFinset (0 : Site d) (n + 1), gammaBr f g x)
      atTop (𝓝 (∑' x, gammaBr f g x)) := by
    have h : HasSum (fun x => gammaBr f g x) (∑' x, gammaBr f g x) := hsfg.hasSum
    exact h.comp hexh
  have hdenom : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun n : ℕ => ∑ x ∈ boxFinset (0 : Site d) (n + 1), gammaBr f g x + V)
      atTop (𝓝 0) := by
    have hcz : Tendsto (fun n : ℕ => c / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hdenom
    refine squeeze_zero_norm' ?_ hcz
    filter_upwards [eventually_ge_atTop N₀] with n hn
    rw [Real.norm_eq_abs]
    exact hbox n (hTsub n (by omega))
  have hlim2 : Tendsto (fun n : ℕ => ∑ x ∈ boxFinset (0 : Site d) (n + 1), gammaBr f g x)
      atTop (𝓝 (-V)) := by
    have := hz.sub_const V
    simpa using this
  exact tendsto_nhds_unique hlim1 hlim2

/-- The Green function decays like `(1 + |x|)^{2-d}` for `d ≥ 3`. -/
private theorem green_decay (hd : 3 ≤ d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Site d,
      |latticeKernel d x| ≤ K * (1 + euclidNorm x) ^ (2 - (d : ℝ)) := by
  obtain ⟨C, R, hR, hasymp⟩ := (LatticeProb.External.potentialKernelAsymptotics_holds d).2 hd
  have hd2 : (2 : ℝ) < d := by exact_mod_cast (by omega : 2 < d)
  have hne : d ≠ 2 := by omega
  have hb : ∀ x : Site d, |latticeKernel d x| = srwGreenInf d x := by
    intro x
    simp only [latticeKernel, if_neg hne]
    rw [abs_neg, abs_of_nonneg (srwGreenInf_nonneg x)]
  set c : ℝ := 2 / (((d : ℝ) - 2) *
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    have hv : 0 ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal :=
      ENNReal.toReal_nonneg
    have : 0 < (d : ℝ) - 2 := by linarith
    positivity
  set M : ℝ := ∑ z ∈ ballFinset d R, srwGreenInf d z with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun z _ => srwGreenInf_nonneg z
  refine ⟨max ((c + |C|) * 2 ^ ((d : ℝ) - 2)) (M * (1 + R) ^ ((d : ℝ) - 2)), ?_, ?_⟩
  · refine le_max_of_le_left ?_
    positivity
  · intro x
    rw [hb]
    have hbase : 0 < 1 + euclidNorm x := by linarith [euclidNorm_nonneg x]
    have hK0 : 0 ≤ (1 + euclidNorm x) ^ (2 - (d : ℝ)) := Real.rpow_nonneg hbase.le _
    by_cases hx : R ≤ euclidNorm x
    · have hx1 : 1 ≤ euclidNorm x := le_trans hR hx
      have hx0 : 0 < euclidNorm x := by linarith
      have h1 := hasymp x hx
      have h2 : srwGreenInf d x ≤ c * euclidNorm x ^ (2 - (d : ℝ)) +
          C * euclidNorm x ^ (-(d : ℝ)) := by
        have := (abs_le.mp h1).2
        linarith
      have h3 : euclidNorm x ^ (-(d : ℝ)) ≤ euclidNorm x ^ (2 - (d : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      have h4 : C * euclidNorm x ^ (-(d : ℝ)) ≤ |C| * euclidNorm x ^ (2 - (d : ℝ)) :=
        calc C * euclidNorm x ^ (-(d : ℝ)) ≤ |C| * euclidNorm x ^ (-(d : ℝ)) :=
              mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hx0.le _)
          _ ≤ |C| * euclidNorm x ^ (2 - (d : ℝ)) :=
              mul_le_mul_of_nonneg_left h3 (abs_nonneg C)
      have h5 : euclidNorm x ^ (2 - (d : ℝ)) ≤
          2 ^ ((d : ℝ) - 2) * (1 + euclidNorm x) ^ (2 - (d : ℝ)) := by
        have h6 : (2 * euclidNorm x) ^ (2 - (d : ℝ)) ≤ (1 + euclidNorm x) ^ (2 - (d : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hbase (by linarith) (by linarith)
        rw [Real.mul_rpow (by norm_num) hx0.le] at h6
        have h7 : (2 : ℝ) ^ (2 - (d : ℝ)) * 2 ^ ((d : ℝ) - 2) = 1 := by
          rw [← Real.rpow_add (by norm_num)]
          simp
        have h8 : 0 ≤ (2 : ℝ) ^ ((d : ℝ) - 2) := by positivity
        calc euclidNorm x ^ (2 - (d : ℝ))
            = 2 ^ ((d : ℝ) - 2) * (2 ^ (2 - (d : ℝ)) * euclidNorm x ^ (2 - (d : ℝ))) := by
              rw [← mul_assoc, mul_comm _ ((2 : ℝ) ^ (2 - (d : ℝ))), h7, one_mul]
          _ ≤ 2 ^ ((d : ℝ) - 2) * (1 + euclidNorm x) ^ (2 - (d : ℝ)) :=
              mul_le_mul_of_nonneg_left h6 h8
      have hcC : 0 ≤ c + |C| := by positivity
      calc srwGreenInf d x ≤ (c + |C|) * euclidNorm x ^ (2 - (d : ℝ)) := by
            nlinarith [h2, h4]
        _ ≤ (c + |C|) * (2 ^ ((d : ℝ) - 2) * (1 + euclidNorm x) ^ (2 - (d : ℝ))) :=
            mul_le_mul_of_nonneg_left h5 hcC
        _ = (c + |C|) * 2 ^ ((d : ℝ) - 2) * (1 + euclidNorm x) ^ (2 - (d : ℝ)) := by ring
        _ ≤ max ((c + |C|) * 2 ^ ((d : ℝ) - 2)) (M * (1 + R) ^ ((d : ℝ) - 2)) *
              (1 + euclidNorm x) ^ (2 - (d : ℝ)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hK0
    · have hxR : euclidNorm x ≤ R := le_of_not_ge hx
      have hxM : srwGreenInf d x ≤ M :=
        Finset.single_le_sum (f := fun z => srwGreenInf d z)
          (fun z _ => srwGreenInf_nonneg z) (mem_ballFinset_iff.mpr hxR)
      have h6 : (1 + R) ^ (2 - (d : ℝ)) ≤ (1 + euclidNorm x) ^ (2 - (d : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hbase (by linarith) (by linarith)
      have h7 : (1 + R) ^ ((d : ℝ) - 2) * (1 + R) ^ (2 - (d : ℝ)) = 1 := by
        rw [← Real.rpow_add (by linarith)]
        simp
      have h8 : 0 ≤ (1 + R) ^ ((d : ℝ)  - 2) := Real.rpow_nonneg (by linarith) _
      calc srwGreenInf d x ≤ M := hxM
        _ = M * (1 + R) ^ ((d : ℝ) - 2) * (1 + R) ^ (2 - (d : ℝ)) := by
            rw [mul_assoc, h7, mul_one]
        _ ≤ M * (1 + R) ^ ((d : ℝ) - 2) * (1 + euclidNorm x) ^ (2 - (d : ℝ)) :=
            mul_le_mul_of_nonneg_left h6 (by positivity)
        _ ≤ max ((c + |C|) * 2 ^ ((d : ℝ) - 2)) (M * (1 + R) ^ ((d : ℝ) - 2)) *
              (1 + euclidNorm x) ^ (2 - (d : ℝ)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hK0

/-- For `d ≥ 3` the kernel is `-G`. -/
private theorem latticeKernel_high (hd : 3 ≤ d) (x : Site d) :
    latticeKernel d x = -srwGreenInf d x := by
  simp only [latticeKernel]
  rw [if_neg (by omega)]

/-- For `d ≥ 3` a translate of the kernel decays like `(1 + |x|)^{2-d}`, with one-step
differences `O((1 + |x|)^{1-d})`. -/
private theorem hi_decays (hd : 3 ≤ d) (y : Site d) :
    Decays d ((d : ℝ) - 2) ((d : ℝ) - 1) (fun z => latticeKernel d (z - y)) := by
  obtain ⟨Cg, hCg, hgrad⟩ := kernel_grad (d := d) (by omega)
  obtain ⟨K, hK, hdec⟩ := green_decay hd
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨Cg * (1 + euclidNorm y) ^ ((d : ℝ) - 1), K * (1 + euclidNorm y) ^ ((d : ℝ) - 2),
    mul_nonneg hCg (Real.rpow_nonneg (by linarith [euclidNorm_nonneg y]) _),
    mul_nonneg hK (Real.rpow_nonneg (by linarith [euclidNorm_nonneg y]) _), ?_, ?_⟩
  · intro x e he
    have h1 := hgrad (x - y) e he
    have h2 := rpow_translate (p := 1 - (d : ℝ)) (by linarith) y x
    have h3 : x + e - y = (x - y) + e := add_sub_right_comm _ _ _
    have h4 : -((d : ℝ) - 1) = 1 - (d : ℝ) := by ring
    have h5 : -(1 - (d : ℝ)) = (d : ℝ) - 1 := by ring
    show |latticeKernel d (x + e - y) - latticeKernel d (x - y)| ≤
      Cg * (1 + euclidNorm y) ^ ((d : ℝ) - 1) * (1 + euclidNorm x) ^ (-((d : ℝ) - 1))
    rw [h4, h3]
    rw [h5] at h2
    calc |latticeKernel d ((x - y) + e) - latticeKernel d (x - y)|
        ≤ Cg * (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)) := h1
      _ ≤ Cg * ((1 + euclidNorm y) ^ ((d : ℝ) - 1) * (1 + euclidNorm x) ^ (1 - (d : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 hCg
      _ = Cg * (1 + euclidNorm y) ^ ((d : ℝ) - 1) * (1 + euclidNorm x) ^ (1 - (d : ℝ)) := by
          ring
  · intro x
    have h1 := hdec (x - y)
    have h2 := rpow_translate (p := 2 - (d : ℝ)) (by linarith) y x
    have h4 : -((d : ℝ) - 2) = 2 - (d : ℝ) := by ring
    have h5 : -(2 - (d : ℝ)) = (d : ℝ) - 2 := by ring
    rw [h4]
    rw [h5] at h2
    calc |latticeKernel d (x - y)|
        ≤ K * (1 + euclidNorm (x - y)) ^ (2 - (d : ℝ)) := h1
      _ ≤ K * ((1 + euclidNorm y) ^ ((d : ℝ) - 2) * (1 + euclidNorm x) ^ (2 - (d : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 hK
      _ = K * (1 + euclidNorm y) ^ ((d : ℝ) - 2) * (1 + euclidNorm x) ^ (2 - (d : ℝ)) := by
          ring

/-- For `d ≥ 3`, the total of `Γ` of two translates of the kernel. -/
private theorem high_tsum (hd : 3 ≤ d) (y y' : Site d) :
    Summable (gammaBr (fun z => latticeKernel d (z - y)) (fun z => latticeKernel d (z - y'))) ∧
    ∑' x, gammaBr (fun z => latticeKernel d (z - y)) (fun z => latticeKernel d (z - y')) x =
      if y = y' then 2 * srwGreenInf d 0 - 1
      else srwGreenInf d (y - y') + srwGreenInf d (y' - y) := by
  have hd2 : 2 ≤ d := by omega
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hT : ∀ z : Site d, ∀ x ∉ ({y, y'} : Finset (Site d)), z = y ∨ z = y' →
      walkOp (fun w => latticeKernel d (w - z)) x - latticeKernel d (x - z) = 0 := by
    intro z x hx hz
    rw [kernel_translate_lap hd2 z x]
    have : x ≠ z := by
      rintro rfl
      exact hx (by rcases hz with rfl | rfl <;> simp)
    simp [this]
  obtain ⟨hs, hv⟩ := tsum_gammaBr (d := d) hd2 (α := (d : ℝ) - 2) (β := (d : ℝ) - 1)
    (by linarith) (by linarith) (hi_decays hd y) (hi_decays hd y') {y, y'}
    (fun x hx => hT y x hx (Or.inl rfl)) (fun x hx => hT y' x hx (Or.inr rfl))
  refine ⟨hs, ?_⟩
  rw [hv]
  simp only [kernel_translate_lap hd2]
  simp only [latticeKernel_high hd]
  by_cases h : y = y'
  · subst h
    simp
    ring
  · rw [Finset.sum_pair h, if_neg h]
    simp [h, Ne.symm h]
    ring

/-- For `d ≥ 3`, every finite partial sum of `Γ` of a translate with itself is at most
`2 G(0) - 1`. -/
private theorem high_V (hd : 3 ≤ d) (y : Site d) (S : Finset (Site d)) :
    ∑ x ∈ S, gammaBr (fun z => latticeKernel d (z - y)) (fun z => latticeKernel d (z - y)) x ≤
      2 * srwGreenInf d 0 - 1 := by
  obtain ⟨hs, hv⟩ := high_tsum hd y y
  rw [if_pos rfl] at hv
  rw [← hv]
  exact hs.sum_le_tsum S fun x _ => gammaBr_self_nonneg (by omega) _ x

/-- A sum of a translate of a nonnegative summable weight over a finite set is at most its
total. -/
private theorem hi_sum_translate_le {h : Site d → ℝ} (h0 : ∀ u, 0 ≤ h u) (hs : Summable h)
    (S : Finset (Site d)) (y : Site d) : ∑ x ∈ S, h (x - y) ≤ ∑' u, h u := by
  have hinj : Set.InjOn (fun x : Site d => x - y) ↑S := fun a _ b _ hab => sub_left_injective hab
  rw [← Finset.sum_image (f := h) (g := fun x : Site d => x - y) hinj]
  exact hs.sum_le_tsum _ fun u _ => h0 u

/-- The bracket of a translate of the kernel with itself is at most the square of the one-step
bound. -/
private theorem hi_gamma_le (hd : 2 ≤ d) {Cg : ℝ}
    (hgrad : ∀ x : Site d, ∀ e ∈ unitSteps d,
      |latticeKernel d (x + e) - latticeKernel d x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (y x : Site d) :
    gammaBr (fun z => latticeKernel d (z - y)) (fun z => latticeKernel d (z - y)) x ≤
      Cg ^ 2 * (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ)) := by
  have hd1 : 1 ≤ d := by omega
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd1
  set m : ℝ := Cg * (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)) with hm
  have hbase : 0 < 1 + euclidNorm (x - y) := by linarith [euclidNorm_nonneg (x - y)]
  have hsq0 : ((1 + euclidNorm (x - y)) ^ (1 - (d : ℝ))) ^ 2 =
      (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
    congr 1
    push_cast
    ring
  have hm2 : m ^ 2 = Cg ^ 2 * (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ)) := by
    rw [hm, mul_pow, hsq0]
  rw [← hm2, gammaBr]
  have hinc : ∀ e ∈ unitSteps d, (latticeKernel d (x + e - y) - latticeKernel d (x - y)) *
      (latticeKernel d (x + e - y) - latticeKernel d (x - y)) ≤ m ^ 2 := by
    intro e he
    have h1 := hgrad (x - y) e he
    rw [← add_sub_right_comm] at h1
    calc (latticeKernel d (x + e - y) - latticeKernel d (x - y)) *
        (latticeKernel d (x + e - y) - latticeKernel d (x - y))
        = |latticeKernel d (x + e - y) - latticeKernel d (x - y)| ^ 2 := by
          rw [sq_abs]; ring
      _ ≤ m ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hsum : ∑ e ∈ unitSteps d, (latticeKernel d (x + e - y) - latticeKernel d (x - y)) *
      (latticeKernel d (x + e - y) - latticeKernel d (x - y)) ≤ 2 * d * m ^ 2 := by
    calc _ ≤ ∑ _e ∈ unitSteps d, m ^ 2 := Finset.sum_le_sum hinc
      _ = 2 * d * m ^ 2 := by rw [Finset.sum_const, card_unitSteps, nsmul_eq_mul]; push_cast; ring
  have hsq : 0 ≤ (walkOp (fun z => latticeKernel d (z - y)) x - latticeKernel d (x - y)) *
      (walkOp (fun z => latticeKernel d (z - y)) x - latticeKernel d (x - y)) :=
    mul_self_nonneg _
  have hle : (1 / (2 * (d : ℝ))) * ∑ e ∈ unitSteps d,
      (latticeKernel d (x + e - y) - latticeKernel d (x - y)) *
        (latticeKernel d (x + e - y) - latticeKernel d (x - y)) ≤ m ^ 2 := by
    calc _ ≤ (1 / (2 * (d : ℝ))) * (2 * d * m ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = m ^ 2 := by field_simp
  linarith

/-- For `d ≥ 3`, the weighted partial sums of `Γ` of a translate with itself. -/
private theorem high_W (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Site d) (r : ℝ), 0 ≤ r → ∀ S : Finset (Site d),
      ∑ x ∈ S, min (euclidNorm x) r *
          gammaBr (fun z => latticeKernel d (z - y)) (fun z => latticeKernel d (z - y)) x ≤
        C * Real.sqrt r * (1 + Real.sqrt (euclidNorm y)) := by
  have hd2 : 2 ≤ d := by omega
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨Cg, hCg, hgrad⟩ := kernel_grad (d := d) hd2
  have hsum : Summable (fun u : Site d => (1 + euclidNorm u) ^ (-(2 * (d : ℝ) - 5 / 2))) :=
    summable_one_add_euclidNorm_rpow d (by linarith)
  set Sm : ℝ := ∑' u : Site d, (1 + euclidNorm u) ^ (-(2 * (d : ℝ) - 5 / 2)) with hSm
  have hSm0 : 0 ≤ Sm :=
    tsum_nonneg fun u => Real.rpow_nonneg (by linarith [euclidNorm_nonneg u]) _
  have hG : 1 ≤ srwGreenInf d 0 := one_le_srwGreenInf_origin hd
  refine ⟨Cg ^ 2 * Sm + (2 * srwGreenInf d 0 - 1), by
    have := mul_nonneg (sq_nonneg Cg) hSm0
    linarith, ?_⟩
  intro y r hr S
  set F : Site d → ℝ := fun z => latticeKernel d (z - y) with hF
  have hpt : ∀ x : Site d, min (euclidNorm x) r * gammaBr F F x ≤
      Real.sqrt r * (Cg ^ 2 * (1 + euclidNorm (x - y)) ^ (-(2 * (d : ℝ) - 5 / 2)) +
        Real.sqrt (euclidNorm y) * gammaBr F F x) := by
    intro x
    have hΓ0 := gammaBr_self_nonneg (by omega : 1 ≤ d) F x
    have hΓle := hi_gamma_le hd2 hgrad y x
    set u : ℝ := euclidNorm (x - y) with hu
    have hu0 : 0 ≤ u := euclidNorm_nonneg _
    have hy0 : 0 ≤ euclidNorm y := euclidNorm_nonneg y
    have hxle : euclidNorm x ≤ u + euclidNorm y := by
      have := euclidNorm_add_le (x - y) y
      rwa [sub_add_cancel] at this
    have hmin : min (euclidNorm x) r ≤ Real.sqrt r * (Real.sqrt u + Real.sqrt (euclidNorm y)) := by
      have hs0 : 0 ≤ Real.sqrt r * (Real.sqrt u + Real.sqrt (euclidNorm y)) := by positivity
      refine le_of_sq_le_sq ?_ hs0
      have h1 : min (euclidNorm x) r ^ 2 ≤ euclidNorm x * r := by
        have hm0 : 0 ≤ min (euclidNorm x) r := le_min (euclidNorm_nonneg x) hr
        calc min (euclidNorm x) r ^ 2 = min (euclidNorm x) r * min (euclidNorm x) r := sq _
          _ ≤ euclidNorm x * r :=
            mul_le_mul (min_le_left _ _) (min_le_right _ _) hm0 (euclidNorm_nonneg x)
      have h2 : (Real.sqrt r * (Real.sqrt u + Real.sqrt (euclidNorm y))) ^ 2 =
          r * (u + euclidNorm y + 2 * (Real.sqrt u * Real.sqrt (euclidNorm y))) := by
        rw [mul_pow, Real.sq_sqrt hr, add_sq, Real.sq_sqrt hu0, Real.sq_sqrt hy0]
        ring
      rw [h2]
      have h3 : 0 ≤ 2 * (Real.sqrt u * Real.sqrt (euclidNorm y)) := by positivity
      calc min (euclidNorm x) r ^ 2 ≤ euclidNorm x * r := h1
        _ ≤ (u + euclidNorm y) * r := mul_le_mul_of_nonneg_right hxle hr
        _ ≤ r * (u + euclidNorm y + 2 * (Real.sqrt u * Real.sqrt (euclidNorm y))) := by
          nlinarith
    have hsqrt : Real.sqrt u ≤ (1 + u) ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow hu0 (by linarith) (by norm_num)
    have hbase : 0 < 1 + u := by linarith
    have hcomb : Real.sqrt u * ((1 + u) ^ (2 - 2 * (d : ℝ))) ≤
        (1 + u) ^ (-(2 * (d : ℝ) - 5 / 2)) := by
      calc Real.sqrt u * ((1 + u) ^ (2 - 2 * (d : ℝ)))
          ≤ (1 + u) ^ ((1 : ℝ) / 2) * ((1 + u) ^ (2 - 2 * (d : ℝ))) :=
            mul_le_mul_of_nonneg_right hsqrt (Real.rpow_nonneg hbase.le _)
        _ = (1 + u) ^ (-(2 * (d : ℝ) - 5 / 2)) := by
            rw [← Real.rpow_add hbase]
            congr 1
            ring
    have hA : Real.sqrt u * gammaBr F F x ≤
        Cg ^ 2 * (1 + u) ^ (-(2 * (d : ℝ) - 5 / 2)) := by
      calc Real.sqrt u * gammaBr F F x ≤ Real.sqrt u * (Cg ^ 2 * (1 + u) ^ (2 - 2 * (d : ℝ))) :=
            mul_le_mul_of_nonneg_left hΓle (Real.sqrt_nonneg _)
        _ = Cg ^ 2 * (Real.sqrt u * (1 + u) ^ (2 - 2 * (d : ℝ))) := by ring
        _ ≤ Cg ^ 2 * (1 + u) ^ (-(2 * (d : ℝ) - 5 / 2)) :=
            mul_le_mul_of_nonneg_left hcomb (sq_nonneg _)
    calc min (euclidNorm x) r * gammaBr F F x
        ≤ (Real.sqrt r * (Real.sqrt u + Real.sqrt (euclidNorm y))) * gammaBr F F x :=
          mul_le_mul_of_nonneg_right hmin hΓ0
      _ = Real.sqrt r * (Real.sqrt u * gammaBr F F x +
            Real.sqrt (euclidNorm y) * gammaBr F F x) := by ring
      _ ≤ Real.sqrt r * (Cg ^ 2 * (1 + u) ^ (-(2 * (d : ℝ) - 5 / 2)) +
            Real.sqrt (euclidNorm y) * gammaBr F F x) :=
          mul_le_mul_of_nonneg_left (add_le_add hA le_rfl) (Real.sqrt_nonneg _)
  have hsumw := hi_sum_translate_le (h := fun u : Site d => (1 + euclidNorm u) ^
    (-(2 * (d : ℝ) - 5 / 2))) (fun u => Real.rpow_nonneg (by linarith [euclidNorm_nonneg u]) _)
    hsum S y
  have hsumV := high_V hd y S
  calc ∑ x ∈ S, min (euclidNorm x) r * gammaBr F F x
      ≤ ∑ x ∈ S, Real.sqrt r * (Cg ^ 2 * (1 + euclidNorm (x - y)) ^ (-(2 * (d : ℝ) - 5 / 2)) +
          Real.sqrt (euclidNorm y) * gammaBr F F x) := Finset.sum_le_sum fun x _ => hpt x
    _ = Real.sqrt r * (Cg ^ 2 * ∑ x ∈ S, (1 + euclidNorm (x - y)) ^ (-(2 * (d : ℝ) - 5 / 2)) +
          Real.sqrt (euclidNorm y) * ∑ x ∈ S, gammaBr F F x) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ Real.sqrt r * (Cg ^ 2 * Sm + Real.sqrt (euclidNorm y) * (2 * srwGreenInf d 0 - 1)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (Real.sqrt_nonneg _)
        · exact mul_le_mul_of_nonneg_left hsumw (sq_nonneg _)
        · exact mul_le_mul_of_nonneg_left hsumV (Real.sqrt_nonneg _)
    _ ≤ (Cg ^ 2 * Sm + (2 * srwGreenInf d 0 - 1)) * Real.sqrt r *
          (1 + Real.sqrt (euclidNorm y)) := by
        have hs0 := Real.sqrt_nonneg r
        have hy0 := Real.sqrt_nonneg (euclidNorm y)
        have hA0 : 0 ≤ Cg ^ 2 * Sm := by positivity
        have hB0 : 0 ≤ 2 * srwGreenInf d 0 - 1 := by linarith
        nlinarith [mul_nonneg hs0 hA0, mul_nonneg hs0 (mul_nonneg hy0 hA0),
          mul_nonneg hs0 hB0, mul_nonneg hs0 (mul_nonneg hy0 hB0)]

/-- The Laplacian of a translate of the kernel is the indicator of the centre. -/
private theorem kernel_translate_D (hd : 2 ≤ d) (y : Site d) (S : Finset (Site d)) :
    ∑ x ∈ S, (walkOp (fun z => latticeKernel d (z - y)) x - latticeKernel d (x - y)) ^ 2 ≤ 1 := by
  have h : ∀ x ∈ S, (walkOp (fun z => latticeKernel d (z - y)) x -
      latticeKernel d (x - y)) ^ 2 = if x = y then 1 else 0 := by
    intro x _
    rw [kernel_translate_lap hd y x]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']
  split_ifs <;> norm_num


/-- The planar dipole `z ↦ b(z - y - k e₁) - b(z - y)`. -/
private noncomputable def dipole (y : Site 2) (k : ℕ) (z : Site 2) : ℝ :=
  latticeKernel 2 (z - (y + (k : ℤ) • unit (0 : Fin 2))) - latticeKernel 2 (z - y)


/-- The Euclidean norm of an integer multiple of a coordinate vector. -/
private theorem pl_norm_smul_unit (i : Fin d) (s : ℤ) :
    euclidNorm (s • unit i) = |(s : ℝ)| := by
  have h : ∀ j : Fin d, (((s • unit i) j : ℤ) : ℝ) ^ 2 = if j = i then (s : ℝ) ^ 2 else 0 := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp [unit]
    · simp [unit, hj]
  rw [euclidNorm]
  simp only [h]
  rw [Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i), Real.sqrt_sq_eq_abs]

/-- The squared Euclidean norm of a planar site. -/
private theorem pl_sq_norm (v : Site 2) :
    euclidNorm v ^ 2 = ((v 0 : ℤ) : ℝ) ^ 2 + ((v 1 : ℤ) : ℝ) ^ 2 := by
  rw [euclidNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Fin.sum_univ_two]

/-- The walk operator is additive. -/
private theorem pl_walkOp_sub (F G : Site d → ℝ) (x : Site d) :
    walkOp (fun z => F z - G z) x = walkOp F x - walkOp G x := by
  rw [walkOp_eq_avg, walkOp_eq_avg, walkOp_eq_avg, ← mul_sub, ← Finset.sum_sub_distrib]

/-- The kernel vanishes at the origin. -/
private theorem pl_kernel_zero : latticeKernel 2 0 = 0 := by
  simp only [latticeKernel, if_true, sub_self]
  exact (tendsto_const_nhds (x := (0 : ℝ))).limUnder_eq

/-- The Laplacian of the planar dipole is `1_{y + k e₁} - 1_{y}`. -/
private theorem pl_lap (y : Site 2) (k : ℕ) (x : Site 2) :
    walkOp (dipole y k) x - dipole y k x =
      (if x = y + (k : ℤ) • unit (0 : Fin 2) then 1 else 0) - (if x = y then 1 else 0) := by
  have h := pl_walkOp_sub (fun z => latticeKernel 2 (z - (y + (k : ℤ) • unit (0 : Fin 2))))
    (fun z => latticeKernel 2 (z - y)) x
  have e1 := kernel_translate_lap (d := 2) le_rfl (y + (k : ℤ) • unit (0 : Fin 2)) x
  have e2 := kernel_translate_lap (d := 2) le_rfl y x
  have hd : dipole y k = fun z => latticeKernel 2 (z - (y + (k : ℤ) • unit (0 : Fin 2))) -
      latticeKernel 2 (z - y) := rfl
  rw [hd, h]
  linarith

/-- For a unit step, the one-step difference of a translate of the kernel at `x` is bounded by
a multiple of `(1 + |x|)^{-1}` depending on the centre. -/
private theorem pl_grad_shift :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ (x y' : Site 2), ∀ e ∈ unitSteps 2,
      |latticeKernel 2 (x - y' + e) - latticeKernel 2 (x - y')| ≤
        Cg * ((1 + euclidNorm y') * (1 + euclidNorm x) ^ (-(1 : ℝ))) := by
  obtain ⟨Cg, hCg, hgrad⟩ := kernel_grad (d := 2) le_rfl
  refine ⟨Cg, hCg, fun x y' e he => ?_⟩
  have h1 := hgrad (x - y') e he
  have h2 := rpow_translate (d := 2) (p := -(1 : ℝ)) (by norm_num) y' x
  rw [neg_neg, Real.rpow_one] at h2
  have e1 : (1 : ℝ) - ((2 : ℕ) : ℝ) = -(1 : ℝ) := by norm_num
  rw [e1] at h1
  refine h1.trans ?_
  calc Cg * (1 + euclidNorm (x - y')) ^ (-(1 : ℝ))
      ≤ Cg * ((1 + euclidNorm y') * (1 + euclidNorm x) ^ (-(1 : ℝ))) :=
        mul_le_mul_of_nonneg_left h2 hCg
    _ = _ := rfl

/-- The planar dipole is a sum of one-step differences of the kernel along the horizontal
axis. -/
private theorem pl_dipole_telescope (y : Site 2) (k : ℕ) (x : Site 2) :
    dipole y k x = ∑ t ∈ Finset.range k,
      (latticeKernel 2 (x - (y + ((t + 1 : ℕ) : ℤ) • unit (0 : Fin 2))) -
        latticeKernel 2 (x - (y + ((t + 1 : ℕ) : ℤ) • unit (0 : Fin 2)) + unit (0 : Fin 2))) := by
  have hs := Finset.sum_range_sub (fun t : ℕ =>
    latticeKernel 2 (x - (y + (t : ℤ) • unit (0 : Fin 2)))) k
  have hcongr : ∑ t ∈ Finset.range k,
      (latticeKernel 2 (x - (y + ((t + 1 : ℕ) : ℤ) • unit (0 : Fin 2))) -
        latticeKernel 2 (x - (y + ((t + 1 : ℕ) : ℤ) • unit (0 : Fin 2)) + unit (0 : Fin 2))) =
      ∑ t ∈ Finset.range k,
        (latticeKernel 2 (x - (y + ((t + 1 : ℕ) : ℤ) • unit (0 : Fin 2))) -
          latticeKernel 2 (x - (y + (t : ℤ) • unit (0 : Fin 2)))) := by
    refine Finset.sum_congr rfl fun t _ => ?_
    have : x - (y + ((t + 1 : ℕ) : ℤ) • unit (0 : Fin 2)) + unit (0 : Fin 2) =
        x - (y + (t : ℤ) • unit (0 : Fin 2)) := by
      push_cast
      module
    rw [this]
  rw [hcongr, hs]
  simp only [dipole, Nat.cast_zero, zero_smul, add_zero]

/-- The planar dipole has decay `O((1+|x|)^{-1})`, with one-step differences of the same order. -/
private theorem pl_decays (y : Site 2) (k : ℕ) : Decays 2 1 1 (dipole y k) := by
  obtain ⟨Cg, hCg, hg⟩ := pl_grad_shift
  have hnn : ∀ v : Site 2, 0 ≤ 1 + euclidNorm v := fun v => by
    have := euclidNorm_nonneg v
    linarith
  refine ⟨Cg * ((1 + euclidNorm (y + (k : ℤ) • unit (0 : Fin 2))) + (1 + euclidNorm y)),
    Cg * ∑ t ∈ Finset.range k, (1 + euclidNorm (y + ((t + 1 : ℕ) : ℤ) • unit (0 : Fin 2))),
    mul_nonneg hCg (add_nonneg (hnn _) (hnn _)),
    mul_nonneg hCg (Finset.sum_nonneg fun t _ => hnn _), ?_, ?_⟩
  · intro x e he
    have h1 := hg x (y + (k : ℤ) • unit (0 : Fin 2)) e he
    have h2 := hg x y e he
    have hsplit : dipole y k (x + e) - dipole y k x =
        (latticeKernel 2 (x - (y + (k : ℤ) • unit (0 : Fin 2)) + e) -
          latticeKernel 2 (x - (y + (k : ℤ) • unit (0 : Fin 2)))) -
        (latticeKernel 2 (x - y + e) - latticeKernel 2 (x - y)) := by
      simp only [dipole, add_sub_right_comm]
      ring
    rw [hsplit]
    refine (abs_sub _ _).trans ?_
    calc _ ≤ Cg * ((1 + euclidNorm (y + (k : ℤ) • unit (0 : Fin 2))) *
          (1 + euclidNorm x) ^ (-(1 : ℝ))) + Cg * ((1 + euclidNorm y) *
          (1 + euclidNorm x) ^ (-(1 : ℝ))) := add_le_add h1 h2
      _ = _ := by ring
  · intro x
    rw [pl_dipole_telescope]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ t ∈ Finset.range k, Cg * ((1 + euclidNorm (y + ((t + 1 : ℕ) : ℤ) •
          unit (0 : Fin 2))) * (1 + euclidNorm x) ^ (-(1 : ℝ))) := by
          refine Finset.sum_le_sum fun t _ => ?_
          rw [abs_sub_comm]
          exact hg x _ _ (mem_unitSteps.mpr ⟨0, Or.inl rfl⟩)
      _ = _ := by
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun t _ => by ring

/-- A sum against the difference of two point masses inside a finite set. -/
private theorem pl_sum_dirac (a y : Site 2) (T : Finset (Site 2)) (ha : a ∈ T) (hy : y ∈ T)
    (h : Site 2 → ℝ) :
    ∑ x ∈ T, h x * ((if x = a then 1 else 0) - (if x = y then 1 else 0)) = h a - h y := by
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', ha,
    hy, if_true]

/-- A positive multiple of a coordinate vector is nonzero. -/
private theorem pl_smul_ne_zero {k : ℕ} (hk : 1 ≤ k) : (k : ℤ) • unit (0 : Fin 2) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [unit] at this
  omega

/-- The total of `Γ` of two planar dipoles, in terms of the values of the dipoles at the
endpoints. -/
private theorem pl_tsum_dipole (y y' : Site 2) (k : ℕ) :
    Summable (gammaBr (dipole y k) (dipole y' k)) ∧
    ∑' x, gammaBr (dipole y k) (dipole y' k) x =
      -((dipole y' k (y + (k : ℤ) • unit (0 : Fin 2)) - dipole y' k y) +
        (dipole y k (y' + (k : ℤ) • unit (0 : Fin 2)) - dipole y k y') +
        (((if y + (k : ℤ) • unit (0 : Fin 2) = y' + (k : ℤ) • unit (0 : Fin 2) then (1 : ℝ)
            else 0) - (if y + (k : ℤ) • unit (0 : Fin 2) = y' then 1 else 0)) -
          ((if y = y' + (k : ℤ) • unit (0 : Fin 2) then (1 : ℝ) else 0) -
            (if y = y' then 1 else 0)))) := by
  set a : Site 2 := y + (k : ℤ) • unit (0 : Fin 2) with ha
  set a' : Site 2 := y' + (k : ℤ) • unit (0 : Fin 2) with ha'
  set T : Finset (Site 2) := {a, y, a', y'} with hT
  have hTf : ∀ x ∉ T, walkOp (dipole y k) x - dipole y k x = 0 := by
    intro x hx
    rw [pl_lap]
    have h1 : x ≠ a := fun h => hx (by simp [hT, h])
    have h2 : x ≠ y := fun h => hx (by simp [hT, h])
    rw [if_neg (show ¬x = y + (k : ℤ) • unit (0 : Fin 2) from h1), if_neg h2, sub_self]
  have hTg : ∀ x ∉ T, walkOp (dipole y' k) x - dipole y' k x = 0 := by
    intro x hx
    rw [pl_lap]
    have h1 : x ≠ a' := fun h => hx (by simp [hT, h])
    have h2 : x ≠ y' := fun h => hx (by simp [hT, h])
    rw [if_neg (show ¬x = y' + (k : ℤ) • unit (0 : Fin 2) from h1), if_neg h2, sub_self]
  obtain ⟨hs, hv⟩ := tsum_gammaBr (d := 2) le_rfl (α := 1) (β := 1) le_rfl
    (by norm_num) (pl_decays y k) (pl_decays y' k) T hTf hTg
  refine ⟨hs, ?_⟩
  rw [hv]
  have hmem : a ∈ T ∧ y ∈ T ∧ a' ∈ T ∧ y' ∈ T := by simp [hT]
  obtain ⟨m1, m2, m3, m4⟩ := hmem
  have e1 : ∑ x ∈ T, (dipole y' k x * (walkOp (dipole y k) x - dipole y k x) +
      dipole y k x * (walkOp (dipole y' k) x - dipole y' k x) +
      (walkOp (dipole y k) x - dipole y k x) * (walkOp (dipole y' k) x - dipole y' k x)) =
      (dipole y' k a - dipole y' k y) + (dipole y k a' - dipole y k y') +
      (((if a = a' then (1 : ℝ) else 0) - (if a = y' then 1 else 0)) -
        ((if y = a' then (1 : ℝ) else 0) - (if y = y' then 1 else 0))) := by
    have p1 := pl_sum_dirac a y T m1 m2 (dipole y' k)
    have p2 := pl_sum_dirac a' y' T m3 m4 (dipole y k)
    have p3 := pl_sum_dirac a y T m1 m2 (fun x => (if x = a' then (1 : ℝ) else 0) -
      (if x = y' then 1 else 0))
    simp only [pl_lap, Finset.sum_add_distrib]
    rw [p1, p2]
    have : ∑ x ∈ T, ((if x = a then (1 : ℝ) else 0) - (if x = y then 1 else 0)) *
        ((if x = a' then (1 : ℝ) else 0) - (if x = y' then 1 else 0)) =
        ∑ x ∈ T, ((if x = a' then (1 : ℝ) else 0) - (if x = y' then 1 else 0)) *
        ((if x = a then (1 : ℝ) else 0) - (if x = y then 1 else 0)) :=
      Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [this, p3]
  rw [e1]

/-- The planar kernel on the horizontal axis is `(2/π) log |m| + κ + O(m^{-2})`. -/
private theorem pl_axis_asymp :
    ∃ κ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ m : ℤ, R ≤ |(m : ℝ)| →
      |latticeKernel 2 (m • unit (0 : Fin 2)) - (2 / Real.pi * Real.log |(m : ℝ)| + κ)| ≤
        C * |(m : ℝ)| ^ (-2 : ℝ) := by
  obtain ⟨κ, C, R, hR, h⟩ := kernel_asymp_two
  refine ⟨κ, max C 0, R, le_max_right _ _, hR, fun m hm => ?_⟩
  have hn := pl_norm_smul_unit (0 : Fin 2) m
  have h1 := h (m • unit (0 : Fin 2)) (by rw [hn]; exact hm)
  rw [hn] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _))

/-- The diagonal total of `Γ` for a planar dipole. -/
private theorem planar_T_diag (k : ℕ) (hk : 1 ≤ k) (y : Site 2) :
    Summable (gammaBr (dipole y k) (dipole y k)) ∧
    ∑' x, gammaBr (dipole y k) (dipole y k) x =
      2 * (latticeKernel 2 ((k : ℤ) • unit (0 : Fin 2)) +
        latticeKernel 2 (-((k : ℤ) • unit (0 : Fin 2)))) - 2 := by
  obtain ⟨hs, hv⟩ := pl_tsum_dipole y y k
  refine ⟨hs, ?_⟩
  rw [hv]
  have hne : y + (k : ℤ) • unit (0 : Fin 2) ≠ y := fun h =>
    pl_smul_ne_zero hk (add_left_cancel (h.trans (add_zero y).symm))
  have hne' : y ≠ y + (k : ℤ) • unit (0 : Fin 2) := fun h => hne h.symm
  simp only [dipole, if_true, hne, hne', if_false, sub_self, add_sub_cancel_left,
    sub_add_cancel_left, pl_kernel_zero]
  ring

/-- Every finite partial sum of `Γ` of a planar dipole with itself is at most its total. -/
private theorem planar_V (k : ℕ) (hk : 1 ≤ k) (y : Site 2) (S : Finset (Site 2)) :
    ∑ x ∈ S, gammaBr (dipole y k) (dipole y k) x ≤
      2 * (latticeKernel 2 ((k : ℤ) • unit (0 : Fin 2)) +
        latticeKernel 2 (-((k : ℤ) • unit (0 : Fin 2)))) - 2 := by
  obtain ⟨hs, hv⟩ := planar_T_diag k hk y
  rw [← hv]
  exact hs.sum_le_tsum S (fun x _ => gammaBr_self_nonneg (by norm_num) _ x)

/-- The Laplacian of a planar dipole has squared mass `2`. -/
private theorem planar_D (k : ℕ) (hk : 1 ≤ k) (y : Site 2) (S : Finset (Site 2)) :
    ∑ x ∈ S, (walkOp (dipole y k) x - dipole y k x) ^ 2 ≤ 2 := by
  have hne : y + (k : ℤ) • unit (0 : Fin 2) ≠ y := fun h =>
    pl_smul_ne_zero hk (add_left_cancel (h.trans (add_zero y).symm))
  set a : Site 2 := y + (k : ℤ) • unit (0 : Fin 2) with ha
  calc ∑ x ∈ S, (walkOp (dipole y k) x - dipole y k x) ^ 2
      = ∑ x ∈ S, ((if x = a then (1 : ℝ) else 0) - (if x = y then 1 else 0)) ^ 2 :=
        Finset.sum_congr rfl fun x _ => by rw [pl_lap]
    _ ≤ ∑ x ∈ S, ((if x = a then (1 : ℝ) else 0) + (if x = y then 1 else 0)) := by
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases h1 : x = a
        · simp [h1, hne]
        · by_cases h2 : x = y
          · simp [h2, hne.symm]
          · simp [h1, h2]
    _ = (if a ∈ S then 1 else 0) + (if y ∈ S then 1 else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    _ ≤ 2 := by
        split_ifs <;> norm_num

/-- The diagonal total grows like `(8/π) log k`. -/
private theorem planar_T_asymp :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      |2 * (latticeKernel 2 ((k : ℤ) • unit (0 : Fin 2)) +
          latticeKernel 2 (-((k : ℤ) • unit (0 : Fin 2)))) - 2 - 8 / Real.pi * Real.log k| ≤ C := by
  obtain ⟨κ, C, R, hC, hR, h⟩ := pl_axis_asymp
  refine ⟨4 * C + 4 * |κ| + 2, by positivity, ⌈R⌉₊, fun k hk => ?_⟩
  have hkR : R ≤ (k : ℝ) := (Nat.le_ceil R).trans (by exact_mod_cast hk)
  have hk1 : (1 : ℝ) ≤ k := hR.trans hkR
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hak : |((k : ℤ) : ℝ)| = k := by rw [Int.cast_natCast]; exact abs_of_nonneg hk0
  have hak' : |((-(k : ℤ) : ℤ) : ℝ)| = k := by
    rw [Int.cast_neg, abs_neg]; exact hak
  have h1 := h (k : ℤ) (by rw [hak]; exact hkR)
  have h2 := h (-(k : ℤ)) (by rw [hak']; exact hkR)
  rw [hak] at h1
  rw [hak', neg_smul] at h2
  have hp : (k : ℝ) ^ (-2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hk1 (by norm_num)
  have hCp : C * (k : ℝ) ^ (-2 : ℝ) ≤ C := by
    calc C * (k : ℝ) ^ (-2 : ℝ) ≤ C * 1 := mul_le_mul_of_nonneg_left hp hC
      _ = C := mul_one _
  have hb1 := abs_le.mp (h1.trans hCp)
  have hb2 := abs_le.mp (h2.trans hCp)
  rw [abs_le]
  have hpi : 8 / Real.pi * Real.log k = 4 * (2 / Real.pi * Real.log k) := by ring
  have hk' : |κ| ≤ |κ| := le_rfl
  have hκ2 := abs_le.mp hk'
  have hκ3 : -|κ| ≤ κ := neg_abs_le κ
  have hκ4 : κ ≤ |κ| := le_abs_self κ
  rw [hpi]
  constructor <;> linarith

/-- The second difference `2 b(τ e₁) - b((τ + k) e₁) - b((τ - k) e₁)` of the kernel on the
horizontal axis. -/
private noncomputable def pl_S (τ : ℤ) (k : ℕ) : ℝ :=
  2 * latticeKernel 2 (τ • unit (0 : Fin 2)) -
    latticeKernel 2 ((τ + k) • unit (0 : Fin 2)) - latticeKernel 2 ((τ - k) • unit (0 : Fin 2))

/-- A negative real power of a positive number. -/
private theorem pl_rpow_neg_two {t : ℝ} (ht : 0 < t) : t ^ (-2 : ℝ) = 1 / t ^ 2 := by
  rw [Real.rpow_neg ht.le, Real.rpow_two, one_div]

/-- If `a b = T² - k²` with `2k ≤ T`, then `2 log T - log a - log b` lies between `0` and
`(4/3) k² / T²`. -/
private theorem pl_log_defect {T k a b : ℝ} (hk : 1 ≤ k) (hT : 2 * k ≤ T) (ha : 0 < a)
    (hb : 0 < b) (hab : a * b = T ^ 2 - k ^ 2) :
    0 ≤ 2 * Real.log T - (Real.log a + Real.log b) ∧
      2 * Real.log T - (Real.log a + Real.log b) ≤ 4 / 3 * k ^ 2 / T ^ 2 := by
  have hTpos : 0 < T := by linarith
  have hk_q : 4 * k ^ 2 ≤ T ^ 2 := by nlinarith
  have hd0 : 0 < T ^ 2 - k ^ 2 := by nlinarith
  have hlog2 : Real.log (T ^ 2) = 2 * Real.log T := by
    rw [Real.log_pow]
    norm_num
  have hL : 2 * Real.log T - (Real.log a + Real.log b) =
      Real.log (T ^ 2 / (T ^ 2 - k ^ 2)) := by
    rw [← Real.log_mul ha.ne' hb.ne', hab, Real.log_div (by positivity) hd0.ne', hlog2]
  rw [hL]
  have hratio : 1 ≤ T ^ 2 / (T ^ 2 - k ^ 2) := by
    rw [le_div_iff₀ hd0]
    nlinarith [sq_nonneg k]
  refine ⟨Real.log_nonneg hratio, ?_⟩
  refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
  have hsub : T ^ 2 / (T ^ 2 - k ^ 2) - 1 = k ^ 2 / (T ^ 2 - k ^ 2) := by
    field_simp
    ring
  rw [hsub, div_le_div_iff₀ hd0 (by positivity)]
  nlinarith [sq_nonneg k]

/-- The bound `|m|^{-2} ≤ 4 / T²` when `|m| ≥ T / 2`. -/
private theorem pl_rpow_le {m T : ℝ} (hT : 0 < T) (hm : T / 2 ≤ |m|) :
    |m| ^ (-2 : ℝ) ≤ 4 / T ^ 2 := by
  have hpos : 0 < |m| := by linarith
  rw [pl_rpow_neg_two hpos, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The algebra behind the second difference bound: if three values are within `c`, `4c`, `4c`
of their logarithmic approximations, and the logarithmic part `L` lies in `[0, 4q/3]`, then
`|2 b₀ - b₁ - b₂| ≤ q + r` whenever `10 c ≤ r`. -/
private theorem pl_S_combine {b0 b1 b2 lT la lb κ L c q r : ℝ}
    (hL : L = 2 * lT - (la + lb)) (hL0 : 0 ≤ L) (hL1 : L ≤ 4 / 3 * q) (hr : 10 * c ≤ r)
    (e0 : |b0 - (2 / Real.pi * lT + κ)| ≤ c) (e1 : |b1 - (2 / Real.pi * la + κ)| ≤ 4 * c)
    (e2 : |b2 - (2 / Real.pi * lb + κ)| ≤ 4 * c) : |2 * b0 - b1 - b2| ≤ q + r := by
  have hpi : (2 / Real.pi) ≤ 2 / 3 := by
    have := Real.pi_gt_three
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) this.le
  have hpi0 : 0 ≤ 2 / Real.pi := by positivity
  have hπL : 2 / Real.pi * L ≤ 2 / 3 * (4 / 3 * q) :=
    mul_le_mul hpi hL1 hL0 (by norm_num)
  have hπL0 : 0 ≤ 2 / Real.pi * L := mul_nonneg hpi0 hL0
  have hid : 2 / Real.pi * L = 2 / Real.pi * (2 * lT) - 2 / Real.pi * la - 2 / Real.pi * lb := by
    rw [hL]
    ring
  have hE0 := abs_le.mp e0
  have hE1 := abs_le.mp e1
  have hE2 := abs_le.mp e2
  rw [abs_le]
  constructor <;> linarith [hE0.1, hE0.2, hE1.1, hE1.2, hE2.1, hE2.2]

/-- The second difference of the kernel on the axis is `O(k² / τ²)` for `|τ| ≥ 2k`. -/
private theorem pl_S_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ τ : ℤ, 2 * (k : ℝ) ≤ |(τ : ℝ)| →
      |pl_S τ k| ≤ K * (k : ℝ) ^ 2 / (τ : ℝ) ^ 2 := by
  obtain ⟨κ, C, R, hC, hR, h⟩ := pl_axis_asymp
  refine ⟨1 + 10 * C, by positivity, ⌈R⌉₊, fun k hk τ hτ => ?_⟩
  have hkR : R ≤ (k : ℝ) := (Nat.le_ceil R).trans (by exact_mod_cast hk)
  have hk1 : (1 : ℝ) ≤ k := hR.trans hkR
  have hkabs : |(k : ℝ)| = k := abs_of_nonneg (by linarith)
  set T : ℝ := |(τ : ℝ)| with hT
  have hTpos : 0 < T := by linarith
  have hτ2 : (τ : ℝ) ^ 2 = T ^ 2 := (sq_abs _).symm
  have hp : T - k ≤ |((τ + k : ℤ) : ℝ)| := by
    have := abs_sub_abs_le_abs_sub (τ : ℝ) ((τ + k : ℤ) : ℝ)
    have e : (τ : ℝ) - ((τ + k : ℤ) : ℝ) = -(k : ℝ) := by push_cast; ring
    rw [e, abs_neg, hkabs] at this
    linarith
  have hm : T - k ≤ |((τ - k : ℤ) : ℝ)| := by
    have := abs_sub_abs_le_abs_sub (τ : ℝ) ((τ - k : ℤ) : ℝ)
    have e : (τ : ℝ) - ((τ - k : ℤ) : ℝ) = (k : ℝ) := by push_cast; ring
    rw [e, hkabs] at this
    linarith
  have hpos1 : 0 < |((τ + k : ℤ) : ℝ)| := by linarith
  have hpos2 : 0 < |((τ - k : ℤ) : ℝ)| := by linarith
  have e0 := h τ (by rw [← hT]; linarith)
  have e1 := h (τ + k) (by linarith)
  have e2 := h (τ - k) (by linarith)
  rw [← hT] at e0
  have hE0 : C * T ^ (-2 : ℝ) = C / T ^ 2 := by rw [pl_rpow_neg_two hTpos]; ring
  have hE1 : C * |((τ + k : ℤ) : ℝ)| ^ (-2 : ℝ) ≤ C * (4 / T ^ 2) :=
    mul_le_mul_of_nonneg_left (pl_rpow_le hTpos (by linarith)) hC
  have hE2 : C * |((τ - k : ℤ) : ℝ)| ^ (-2 : ℝ) ≤ C * (4 / T ^ 2) :=
    mul_le_mul_of_nonneg_left (pl_rpow_le hTpos (by linarith)) hC
  have hprod : |((τ + k : ℤ) : ℝ)| * |((τ - k : ℤ) : ℝ)| = T ^ 2 - (k : ℝ) ^ 2 := by
    rw [← abs_mul]
    push_cast
    rw [show ((τ : ℝ) + k) * ((τ : ℝ) - k) = (τ : ℝ) ^ 2 - (k : ℝ) ^ 2 by ring, hτ2]
    have : (k : ℝ) ^ 2 < T ^ 2 := by nlinarith
    exact abs_of_pos (by linarith)
  obtain ⟨hL0, hL1⟩ := pl_log_defect hk1 hτ hpos1 hpos2 hprod
  set L := 2 * Real.log T - (Real.log |((τ + k : ℤ) : ℝ)| + Real.log |((τ - k : ℤ) : ℝ)|)
    with hL
  have hkk : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hCT : 10 * (C / T ^ 2) ≤ 10 * C * (k : ℝ) ^ 2 / T ^ 2 := by
    have : 10 * (C / T ^ 2) = 10 * C / T ^ 2 := by ring
    rw [this]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    nlinarith
  have h4 : C * (4 / T ^ 2) = 4 * (C / T ^ 2) := by ring
  have hbig : (1 + 10 * C) * (k : ℝ) ^ 2 / T ^ 2 =
      (k : ℝ) ^ 2 / T ^ 2 + 10 * C * (k : ℝ) ^ 2 / T ^ 2 := by ring
  have hcomb := pl_S_combine (b0 := latticeKernel 2 (τ • unit (0 : Fin 2)))
    (b1 := latticeKernel 2 ((τ + k) • unit (0 : Fin 2)))
    (b2 := latticeKernel 2 ((τ - k) • unit (0 : Fin 2))) (κ := κ) (L := L) (c := C / T ^ 2)
    (q := (k : ℝ) ^ 2 / T ^ 2) (r := 10 * C * (k : ℝ) ^ 2 / T ^ 2) hL hL0
    (by rw [← mul_div_assoc]; exact hL1)
    hCT
    (by rw [← hE0]; exact e0) (by rw [← h4]; exact e1.trans hE1)
    (by rw [← h4]; exact e2.trans hE2)
  rw [hτ2, pl_S, hbig]
  exact hcomb

/-- Two integer multiples of the first coordinate vector are equal only if the integers are. -/
private theorem pl_axis_eq {m n : ℤ} (h : m • unit (0 : Fin 2) = n • unit (0 : Fin 2)) :
    m = n := by
  have := congrFun h 0
  simpa [unit] using this

/-- The total of `Γ` of two well separated planar dipoles on the horizontal axis. -/
private theorem planar_T_off :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ s s' : ℤ, 2 * (k : ℤ) ≤ |s - s'| →
      Summable (gammaBr (dipole (s • unit (0 : Fin 2)) k) (dipole (s' • unit (0 : Fin 2)) k)) ∧
      |∑' x, gammaBr (dipole (s • unit (0 : Fin 2)) k) (dipole (s' • unit (0 : Fin 2)) k) x| ≤
        C * (k : ℝ) ^ 2 / ((s - s' : ℤ) : ℝ) ^ 2 := by
  obtain ⟨K, hK, k₀, hS⟩ := pl_S_bound
  refine ⟨2 * K, by positivity, max k₀ 1, fun k hk s s' hss => ?_⟩
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
  have hkk : k₀ ≤ k := le_trans (le_max_left _ _) hk
  obtain ⟨hs, hv⟩ := pl_tsum_dipole (s • unit (0 : Fin 2)) (s' • unit (0 : Fin 2)) k
  refine ⟨hs, ?_⟩
  rw [hv]
  set τ : ℤ := s - s' with hτ
  have hτ' : τ ≤ -(2 * (k : ℤ)) ∨ 2 * (k : ℤ) ≤ τ := le_abs'.mp hss
  have p1 :
      s • unit (0 : Fin 2) + (k : ℤ) • unit (0 : Fin 2) -
        (s' • unit (0 : Fin 2) + (k : ℤ) • unit (0 : Fin 2)) =
        τ • unit (0 : Fin 2) := by
    rw [hτ]
    module
  have p2 :
      s • unit (0 : Fin 2) + (k : ℤ) • unit (0 : Fin 2) - s' • unit (0 : Fin 2) =
        (τ + k) • unit (0 : Fin 2) := by
    rw [hτ]
    module
  have p3 :
      s • unit (0 : Fin 2) - (s' • unit (0 : Fin 2) + (k : ℤ) • unit (0 : Fin 2)) =
        (τ - k) • unit (0 : Fin 2) := by
    rw [hτ]
    module
  have p4 :
      s • unit (0 : Fin 2) - s' • unit (0 : Fin 2) =
        τ • unit (0 : Fin 2) := by
    rw [hτ]
    module
  have q1 :
      s' • unit (0 : Fin 2) + (k : ℤ) • unit (0 : Fin 2) -
        (s • unit (0 : Fin 2) + (k : ℤ) • unit (0 : Fin 2)) =
        (-τ) • unit (0 : Fin 2) := by
    rw [hτ]
    module
  have q2 :
      s' • unit (0 : Fin 2) + (k : ℤ) • unit (0 : Fin 2) - s • unit (0 : Fin 2) =
        (-τ + k) • unit (0 : Fin 2) := by
    rw [hτ]
    module
  have q3 :
      s' • unit (0 : Fin 2) - (s • unit (0 : Fin 2) + (k : ℤ) • unit (0 : Fin 2)) =
        (-τ - k) • unit (0 : Fin 2) := by
    rw [hτ]
    module
  have q4 :
      s' • unit (0 : Fin 2) - s • unit (0 : Fin 2) =
        (-τ) • unit (0 : Fin 2) := by
    rw [hτ]
    module
  have c1 : ¬ s • unit (0 : Fin 2) + (k : ℤ) • unit (0 : Fin 2) =
      s' • unit (0 : Fin 2) + (k : ℤ) • unit (0 : Fin 2) := by
    intro h
    rw [← add_smul, ← add_smul] at h
    have := pl_axis_eq h
    omega
  have c2 : ¬ s • unit (0 : Fin 2) + (k : ℤ) • unit (0 : Fin 2) = s' • unit (0 : Fin 2) := by
    intro h
    rw [← add_smul] at h
    have := pl_axis_eq h
    omega
  have c3 : ¬ s • unit (0 : Fin 2) = s' • unit (0 : Fin 2) + (k : ℤ) • unit (0 : Fin 2) := by
    intro h
    rw [← add_smul] at h
    have := pl_axis_eq h
    omega
  have c4 : ¬ s • unit (0 : Fin 2) = s' • unit (0 : Fin 2) := by
    intro h
    have := pl_axis_eq h
    omega
  have hval : dipole (s' • unit (0 : Fin 2)) k
        (s • unit (0 : Fin 2) + (k : ℤ) • unit (0 : Fin 2)) -
        dipole (s' • unit (0 : Fin 2)) k (s • unit (0 : Fin 2)) +
      (dipole (s • unit (0 : Fin 2)) k (s' • unit (0 : Fin 2) + (k : ℤ) • unit (0 : Fin 2)) -
        dipole (s • unit (0 : Fin 2)) k (s' • unit (0 : Fin 2))) =
      pl_S τ k + pl_S (-τ) k := by
    simp only [dipole, pl_S, p1, p2, p3, p4, q1, q2, q3, q4]
    ring
  rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4, hval]
  have hcast : (2 : ℝ) * (k : ℝ) ≤ |((τ : ℤ) : ℝ)| := by
    have : (2 * (k : ℤ)) ≤ |τ| := hss
    exact_mod_cast this
  have hcast' : (2 : ℝ) * (k : ℝ) ≤ |((-τ : ℤ) : ℝ)| := by
    rw [Int.cast_neg, abs_neg]
    exact hcast
  have b1 := hS k hkk τ hcast
  have b2 := hS k hkk (-τ) hcast'
  rw [Int.cast_neg, neg_sq] at b2
  simp only [sub_self, add_zero]
  rw [abs_neg]
  refine (abs_add_le _ _).trans ?_
  have : 2 * K * (k : ℝ) ^ 2 / (τ : ℝ) ^ 2 =
      K * (k : ℝ) ^ 2 / (τ : ℝ) ^ 2 + K * (k : ℝ) ^ 2 / (τ : ℝ) ^ 2 := by ring
  rw [this]
  exact add_le_add b1 b2

/-- The logarithm of a ratio close to one: if `|AD - BC| ≤ BC/2` then
`|log A + log D - log B - log C| ≤ 2 |AD - BC| / (BC)`. -/
private theorem pl_log_ratio_le {A B C D : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hD : 0 < D) (h : |A * D - B * C| ≤ B * C / 2) :
    |Real.log A + Real.log D - Real.log B - Real.log C| ≤ 2 * |A * D - B * C| / (B * C) := by
  have hBC : 0 < B * C := mul_pos hB hC
  have hρpos : 0 < A * D / (B * C) := div_pos (mul_pos hA hD) hBC
  have hlog : Real.log A + Real.log D - Real.log B - Real.log C =
      Real.log (A * D / (B * C)) := by
    rw [Real.log_div (mul_pos hA hD).ne' hBC.ne', Real.log_mul hA.ne' hD.ne',
      Real.log_mul hB.ne' hC.ne']
    ring
  have hρ1 : A * D / (B * C) - 1 = (A * D - B * C) / (B * C) := by
    field_simp
  have habs : |A * D / (B * C) - 1| ≤ 1 / 2 := by
    rw [hρ1, abs_div, abs_of_pos hBC, div_le_iff₀ hBC]
    linarith
  have hhalf : 1 / 2 ≤ A * D / (B * C) := by
    have := (abs_le.mp habs).1
    linarith
  rw [hlog]
  set ρ := A * D / (B * C) with hρ
  have hup := Real.log_le_sub_one_of_pos hρpos
  have hlow := Real.one_sub_inv_le_log_of_pos hρpos
  have hfin : 2 * |A * D - B * C| / (B * C) = 2 * |ρ - 1| := by
    rw [hρ1, abs_div, abs_of_pos hBC]
    ring
  rw [hfin, abs_le]
  have hinv : 1 - ρ⁻¹ = (ρ - 1) * ρ⁻¹ := by
    field_simp
  have hinv2 : ρ⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hρpos]
    linarith
  have hinv0 : 0 ≤ ρ⁻¹ := inv_nonneg.mpr hρpos.le
  constructor
  · by_cases hρ1' : 1 ≤ ρ
    · have : ρ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hρ1'
      have := abs_nonneg (ρ - 1)
      linarith
    · have hρ1'' := not_le.mp hρ1'
      have h1 : (ρ - 1) * 2 ≤ (ρ - 1) * ρ⁻¹ :=
        mul_le_mul_of_nonpos_left hinv2 (by linarith)
      rw [abs_of_neg (by linarith)]
      linarith
  · have := le_abs_self (ρ - 1)
    have := abs_nonneg (ρ - 1)
    linarith

/-- Polynomial bounds for the four squared norms entering the second difference of the logarithm
of the Euclidean norm: with `D = p² + q² ≥ 100`, each of `A`, `B`, `C` is at least `D/2`
and `|AD - BC| ≤ 5 D`. -/
private theorem pl_four_case {p q a b : ℝ} (hD : 100 ≤ p ^ 2 + q ^ 2)
    (h : (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1)) :
    (p ^ 2 + q ^ 2) / 2 ≤ (p - 1 + a) ^ 2 + (q + b) ^ 2 ∧
    (p ^ 2 + q ^ 2) / 2 ≤ (p - 1) ^ 2 + q ^ 2 ∧
    (p ^ 2 + q ^ 2) / 2 ≤ (p + a) ^ 2 + (q + b) ^ 2 ∧
    |((p - 1 + a) ^ 2 + (q + b) ^ 2) * (p ^ 2 + q ^ 2) -
      ((p - 1) ^ 2 + q ^ 2) * ((p + a) ^ 2 + (q + b) ^ 2)| ≤ 5 * (p ^ 2 + q ^ 2) := by
  have hB : (p ^ 2 + q ^ 2) / 2 ≤ (p - 1) ^ 2 + q ^ 2 := by
    nlinarith [sq_nonneg (p - 8)]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨by nlinarith, hB, by nlinarith [sq_nonneg (p + 8)], ?_⟩
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg p, sq_nonneg q]
  · refine ⟨by nlinarith [sq_nonneg (p - 16)], hB, by nlinarith [sq_nonneg (p - 8)], ?_⟩
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (p - 8), sq_nonneg q]
  · refine ⟨by nlinarith [sq_nonneg (p - 8), sq_nonneg (q + 8)], hB,
      by nlinarith [sq_nonneg (q + 8)], ?_⟩
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (p - 1), sq_nonneg (q + 1), sq_nonneg (p - q),
      sq_nonneg (p + q), sq_nonneg p, sq_nonneg q]
  · refine ⟨by nlinarith [sq_nonneg (p - 8), sq_nonneg (q - 8)], hB,
      by nlinarith [sq_nonneg (q - 8)], ?_⟩
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (p - 1), sq_nonneg (q - 1), sq_nonneg (p - q),
      sq_nonneg (p + q), sq_nonneg p, sq_nonneg q]

/-- The coordinates of a unit step of the plane. -/
private theorem pl_unit_coords {e : Site 2} (he : e ∈ unitSteps 2) :
    (((e 0 : ℤ) : ℝ) = 1 ∧ ((e 1 : ℤ) : ℝ) = 0) ∨
      (((e 0 : ℤ) : ℝ) = -1 ∧ ((e 1 : ℤ) : ℝ) = 0) ∨
      (((e 0 : ℤ) : ℝ) = 0 ∧ ((e 1 : ℤ) : ℝ) = 1) ∨
      (((e 0 : ℤ) : ℝ) = 0 ∧ ((e 1 : ℤ) : ℝ) = -1) := by
  obtain ⟨i, rfl | rfl⟩ := mem_unitSteps.mp he
  · fin_cases i
    · left
      simp [unit]
    · right; right; left
      simp [unit]
  · fin_cases i
    · right; left
      simp [unit]
    · right; right; right
      simp [unit]

/-- The squared norm of a shifted planar site, in coordinates. -/
private theorem pl_sq_norm_shift (w e : Site 2) :
    euclidNorm (w - unit (0 : Fin 2) + e) ^ 2 =
      (((w 0 : ℤ) : ℝ) - 1 + ((e 0 : ℤ) : ℝ)) ^ 2 + (((w 1 : ℤ) : ℝ) + ((e 1 : ℤ) : ℝ)) ^ 2 := by
  rw [pl_sq_norm]
  simp [unit]

/-- The squared norm of a planar site shifted by `-e₁`, in coordinates. -/
private theorem pl_sq_norm_sub_unit (w : Site 2) :
    euclidNorm (w - unit (0 : Fin 2)) ^ 2 = (((w 0 : ℤ) : ℝ) - 1) ^ 2 + ((w 1 : ℤ) : ℝ) ^ 2 := by
  rw [pl_sq_norm]
  simp [unit]

/-- The squared norm of a planar site shifted by a step, in coordinates. -/
private theorem pl_sq_norm_add (w e : Site 2) :
    euclidNorm (w + e) ^ 2 =
      (((w 0 : ℤ) : ℝ) + ((e 0 : ℤ) : ℝ)) ^ 2 + (((w 1 : ℤ) : ℝ) + ((e 1 : ℤ) : ℝ)) ^ 2 := by
  rw [pl_sq_norm]
  simp

/-- A nonnegative real with square at least `50` is positive. -/
private theorem pl_pos_of_sq {t : ℝ} (h0 : 0 ≤ t) (h : 50 ≤ t ^ 2) : 0 < t := by
  rcases h0.eq_or_lt with h1 | h1
  · rw [← h1] at h
    norm_num at h
  · exact h1

/-- The second difference of the logarithm of the Euclidean norm is `O(|w|^{-2})`. -/
private theorem pl_log_second_diff {w e : Site 2} (he : e ∈ unitSteps 2)
    (hw : 10 ≤ euclidNorm w) :
    |Real.log (euclidNorm (w - unit (0 : Fin 2) + e)) -
        Real.log (euclidNorm (w - unit (0 : Fin 2))) - Real.log (euclidNorm (w + e)) +
        Real.log (euclidNorm w)| ≤ 20 / euclidNorm w ^ 2 := by
  have hcoord := pl_unit_coords he
  have hA := pl_sq_norm_shift w e
  have hB := pl_sq_norm_sub_unit w
  have hC := pl_sq_norm_add w e
  have hD := pl_sq_norm w
  have hD100 : 100 ≤ ((w 0 : ℤ) : ℝ) ^ 2 + ((w 1 : ℤ) : ℝ) ^ 2 := by
    rw [← hD]
    nlinarith [euclidNorm_nonneg w]
  obtain ⟨h1, h2, h3, h4⟩ := pl_four_case hD100 hcoord
  rw [← hA, ← hD] at h1
  rw [← hB, ← hD] at h2
  rw [← hC, ← hD] at h3
  rw [← hA, ← hB, ← hC, ← hD] at h4
  set nA := euclidNorm (w - unit (0 : Fin 2) + e) with hnA
  set nB := euclidNorm (w - unit (0 : Fin 2)) with hnB
  set nC := euclidNorm (w + e) with hnC
  set nD := euclidNorm w with hnD
  have hD2 : 100 ≤ nD ^ 2 := by rw [hD]; exact hD100
  have pA : 0 < nA := pl_pos_of_sq (euclidNorm_nonneg _) (by linarith)
  have pB : 0 < nB := pl_pos_of_sq (euclidNorm_nonneg _) (by linarith)
  have pC : 0 < nC := pl_pos_of_sq (euclidNorm_nonneg _) (by linarith)
  have pD : 0 < nD := by linarith
  have hBC : nD ^ 2 / 2 * (nD ^ 2 / 2) ≤ nB ^ 2 * nC ^ 2 :=
    mul_le_mul h2 h3 (by positivity) (by positivity)
  have hcond : |nA ^ 2 * nD ^ 2 - nB ^ 2 * nC ^ 2| ≤ nB ^ 2 * nC ^ 2 / 2 := by
    refine h4.trans ?_
    nlinarith
  have hlog := pl_log_ratio_le (pow_pos pA 2) (pow_pos pB 2) (pow_pos pC 2) (pow_pos pD 2) hcond
  have hbound : 2 * |nA ^ 2 * nD ^ 2 - nB ^ 2 * nC ^ 2| / (nB ^ 2 * nC ^ 2) ≤ 40 / nD ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hl : ∀ t : ℝ, Real.log (t ^ 2) = 2 * Real.log t := fun t => by
    rw [Real.log_pow]
    norm_num
  rw [hl, hl, hl, hl] at hlog
  have := hlog.trans hbound
  have e2 : Real.log nA - Real.log nB - Real.log nC + Real.log nD =
      (2 * Real.log nA + 2 * Real.log nD - 2 * Real.log nB - 2 * Real.log nC) / 2 := by ring
  rw [e2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_le_iff₀ (by norm_num)]
  calc _ ≤ 40 / nD ^ 2 := this
    _ = 20 / nD ^ 2 * 2 := by ring

/-- The norm of a shifted site is at least the norm minus the norm of the shift. -/
private theorem pl_norm_ge (v u : Site 2) : euclidNorm v - euclidNorm u ≤ euclidNorm (v + u) := by
  have := euclidNorm_sub_le (v + u) u
  rw [add_sub_cancel_right] at this
  linarith

/-- Shifting by a vector of norm at most `2` changes the norm by at most `2`. -/
private theorem pl_norm_lower (w u : Site 2) (hu : euclidNorm u ≤ 2) :
    euclidNorm w - 2 ≤ euclidNorm (w + u) := by
  have := pl_norm_ge w u
  linarith

/-- The second difference of the planar kernel is `O(|w|^{-2})`. -/
private theorem pl_hess :
    ∃ K R : ℝ, 0 ≤ K ∧ 1 ≤ R ∧ ∀ w : Site 2, R ≤ euclidNorm w → ∀ e ∈ unitSteps 2,
      |latticeKernel 2 (w - unit (0 : Fin 2) + e) - latticeKernel 2 (w - unit (0 : Fin 2)) -
        latticeKernel 2 (w + e) + latticeKernel 2 w| ≤ K / euclidNorm w ^ 2 := by
  obtain ⟨κ, C, Rb, hRb, h⟩ := kernel_asymp_two
  set Cm : ℝ := max C 0 with hCm
  have hCm0 : 0 ≤ Cm := le_max_right _ _
  refine ⟨14 + 16 * Cm, max (Rb + 2) 10, by positivity,
    le_trans (by norm_num) (le_max_right _ _), fun w hw e he => ?_⟩
  have hn10 : 10 ≤ euclidNorm w := le_trans (le_max_right _ _) hw
  have hnRb : Rb + 2 ≤ euclidNorm w := le_trans (le_max_left _ _) hw
  set n : ℝ := euclidNorm w with hn
  have hnpos : 0 < n := by linarith
  have hu1 : euclidNorm (unit (0 : Fin 2)) = 1 :=
    euclidNorm_of_mem_unitSteps (mem_unitSteps.mpr ⟨0, Or.inl rfl⟩)
  have hue : euclidNorm e = 1 := euclidNorm_of_mem_unitSteps he
  have hE : ∀ v : Site 2, n - 2 ≤ euclidNorm v →
      |latticeKernel 2 v - (2 / Real.pi * Real.log (euclidNorm v) + κ)| ≤ Cm * (4 / n ^ 2) := by
    intro v hv
    have h1 := h v (by linarith)
    have h2 : euclidNorm v ^ (-2 : ℝ) ≤ 4 / n ^ 2 := by
      have := pl_rpow_le (m := euclidNorm v) hnpos (by
        rw [abs_of_nonneg (euclidNorm_nonneg v)]; linarith)
      rwa [abs_of_nonneg (euclidNorm_nonneg v)] at this
    refine h1.trans ?_
    calc C * euclidNorm v ^ (-2 : ℝ) ≤ Cm * euclidNorm v ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (euclidNorm_nonneg _) _)
      _ ≤ Cm * (4 / n ^ 2) := mul_le_mul_of_nonneg_left h2 hCm0
  have hvA : n - 2 ≤ euclidNorm (w - unit (0 : Fin 2) + e) := by
    have : w - unit (0 : Fin 2) + e = w + (e - unit (0 : Fin 2)) := by abel
    rw [this]
    refine pl_norm_lower w _ ?_
    have := euclidNorm_sub_le e (unit (0 : Fin 2))
    linarith
  have hvB : n - 2 ≤ euclidNorm (w - unit (0 : Fin 2)) := by
    have : w - unit (0 : Fin 2) = w + (-unit (0 : Fin 2)) := by abel
    rw [this]
    refine pl_norm_lower w _ ?_
    rw [CERW.Generic.Lattice.euclidNorm_neg, hu1]
    norm_num
  have hvC : n - 2 ≤ euclidNorm (w + e) := pl_norm_lower w e (by rw [hue]; norm_num)
  have hvD : n - 2 ≤ euclidNorm w := by linarith
  have eA := abs_le.mp (hE _ hvA)
  have eB := abs_le.mp (hE _ hvB)
  have eC := abs_le.mp (hE _ hvC)
  have eD := abs_le.mp (hE _ hvD)
  have hX := abs_le.mp (pl_log_second_diff he hn10)
  have hpi : (2 / Real.pi) ≤ 2 / 3 := by
    have := Real.pi_gt_three
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) this.le
  have hpi0 : 0 ≤ 2 / Real.pi := by positivity
  have hp20 : 0 ≤ 20 / n ^ 2 := by positivity
  have hu : 2 / Real.pi * (Real.log (euclidNorm (w - unit (0 : Fin 2) + e)) -
        Real.log (euclidNorm (w - unit (0 : Fin 2))) - Real.log (euclidNorm (w + e)) +
        Real.log (euclidNorm w)) ≤ 2 / 3 * (20 / n ^ 2) :=
    (mul_le_mul_of_nonneg_left hX.2 hpi0).trans
      (mul_le_mul_of_nonneg_right hpi hp20)
  have hl : -(2 / 3 * (20 / n ^ 2)) ≤
      2 / Real.pi * (Real.log (euclidNorm (w - unit (0 : Fin 2) + e)) -
        Real.log (euclidNorm (w - unit (0 : Fin 2))) - Real.log (euclidNorm (w + e)) +
        Real.log (euclidNorm w)) := by
    have h1 := mul_le_mul_of_nonneg_left hX.1 hpi0
    have h2 := mul_le_mul_of_nonneg_right hpi hp20
    have h3 : 2 / Real.pi * (-(20 / n ^ 2)) = -(2 / Real.pi * (20 / n ^ 2)) := by ring
    linarith
  have hid : 2 / Real.pi * (Real.log (euclidNorm (w - unit (0 : Fin 2) + e)) -
        Real.log (euclidNorm (w - unit (0 : Fin 2))) - Real.log (euclidNorm (w + e)) +
        Real.log (euclidNorm w)) =
      2 / Real.pi * Real.log (euclidNorm (w - unit (0 : Fin 2) + e)) -
        2 / Real.pi * Real.log (euclidNorm (w - unit (0 : Fin 2))) -
        2 / Real.pi * Real.log (euclidNorm (w + e)) + 2 / Real.pi * Real.log (euclidNorm w) := by
    ring
  have hfin : (14 + 16 * Cm) / n ^ 2 = 14 / n ^ 2 + 16 * (Cm * (1 / n ^ 2)) := by ring
  rw [abs_le]
  clear_value n
  generalize latticeKernel 2 (w - unit (0 : Fin 2) + e) = bA at *
  generalize latticeKernel 2 (w - unit (0 : Fin 2)) = bB at *
  generalize latticeKernel 2 (w + e) = bC at *
  generalize latticeKernel 2 w = bD at *
  generalize Real.log (euclidNorm (w - unit (0 : Fin 2) + e)) = lA at *
  generalize Real.log (euclidNorm (w - unit (0 : Fin 2))) = lB at *
  generalize Real.log (euclidNorm (w + e)) = lC at *
  generalize Real.log (euclidNorm w) = lD at *
  simp only [div_eq_mul_inv] at *
  generalize (n ^ 2)⁻¹ = v at *
  constructor <;> linarith

/-- The one-step differences of the planar dipole decay like `k / |x - y|²` outside the ball of
radius `3k` around `y`. -/
private theorem pl_dipole_diff :
    ∃ K₃ : ℝ, 0 ≤ K₃ ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ x y : Site 2, ∀ e ∈ unitSteps 2,
      3 * (k : ℝ) ≤ euclidNorm (x - y) →
        |dipole y k (x + e) - dipole y k x| ≤ K₃ * k / euclidNorm (x - y) ^ 2 := by
  obtain ⟨K, R, hK, hR, hH⟩ := pl_hess
  refine ⟨9 / 4 * K, by positivity, ⌈R⌉₊, fun k hk x y e he hxy => ?_⟩
  have hkR : R ≤ (k : ℝ) := (Nat.le_ceil R).trans (by exact_mod_cast hk)
  have hk1 : (1 : ℝ) ≤ k := hR.trans hkR
  set u : Site 2 := x - y with hu
  have hupos : 0 < euclidNorm u := by linarith
  set ψ : ℕ → ℝ := fun t => latticeKernel 2 (u - (t : ℤ) • unit (0 : Fin 2) + e) -
    latticeKernel 2 (u - (t : ℤ) • unit (0 : Fin 2)) with hψ
  have hdiff : dipole y k (x + e) - dipole y k x = ψ k - ψ 0 := by
    have a1 : x + e - (y + (k : ℤ) • unit (0 : Fin 2)) = u - (k : ℤ) • unit (0 : Fin 2) + e := by
      rw [hu]; module
    have a2 : x + e - y = u - ((0 : ℕ) : ℤ) • unit (0 : Fin 2) + e := by
      rw [hu]; simp only [Nat.cast_zero, zero_smul, sub_zero]; abel
    have a3 : x - (y + (k : ℤ) • unit (0 : Fin 2)) = u - (k : ℤ) • unit (0 : Fin 2) := by
      rw [hu]; module
    have a4 : x - y = u - ((0 : ℕ) : ℤ) • unit (0 : Fin 2) := by
      rw [hu]; simp
    simp only [dipole, a1, a2, a3, a4, hψ]
    ring
  have hterm : ∀ t ∈ Finset.range k,
      |ψ (t + 1) - ψ t| ≤ 9 / 4 * K / euclidNorm u ^ 2 := by
    intro t ht
    have ht' : (t : ℝ) ≤ k := by exact_mod_cast (Finset.mem_range.mp ht).le
    set w : Site 2 := u - (t : ℤ) • unit (0 : Fin 2) with hw
    have hw1 : u - ((t + 1 : ℕ) : ℤ) • unit (0 : Fin 2) = w - unit (0 : Fin 2) := by
      rw [hw]; push_cast; module
    have hψt : ψ (t + 1) - ψ t = latticeKernel 2 (w - unit (0 : Fin 2) + e) -
        latticeKernel 2 (w - unit (0 : Fin 2)) - latticeKernel 2 (w + e) +
        latticeKernel 2 w := by
      simp only [hψ, hw1]
      ring
    have hwn : euclidNorm u - t ≤ euclidNorm w := by
      have h1 := pl_norm_ge u ((-(t : ℤ)) • unit (0 : Fin 2))
      have h2 : euclidNorm ((-(t : ℤ)) • unit (0 : Fin 2)) = t := by
        rw [pl_norm_smul_unit, Int.cast_neg, abs_neg, Int.cast_natCast,
          abs_of_nonneg (Nat.cast_nonneg t)]
      have h3 : u + (-(t : ℤ)) • unit (0 : Fin 2) = w := by rw [hw]; module
      rw [h2, h3] at h1
      exact h1
    have hw23 : 2 / 3 * euclidNorm u ≤ euclidNorm w := by linarith
    have hwR : R ≤ euclidNorm w := by linarith
    rw [hψt]
    refine (hH w hwR e he).trans ?_
    have hwpos : 0 < euclidNorm w := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 / 3 * euclidNorm u) ^ 2 ≤ euclidNorm w ^ 2 :=
      pow_le_pow_left₀ (by positivity) hw23 2
    nlinarith [mul_nonneg hK (sq_nonneg (euclidNorm u))]
  rw [hdiff, ← Finset.sum_range_sub ψ k]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (k : ℝ) * (9 / 4 * K / euclidNorm u ^ 2) = 9 / 4 * K * k / euclidNorm u ^ 2 := by ring
  rw [this]

/-- A bound for the self bracket by the squared increments. -/
private theorem pl_gamma_le_sq {f : Site 2 → ℝ} {x : Site 2} {M : ℝ}
    (hM : ∀ e ∈ unitSteps 2, |f (x + e) - f x| ≤ M) : gammaBr f f x ≤ M ^ 2 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (unit 0) (mem_unitSteps.mpr ⟨0, Or.inl rfl⟩))
  have hcard : ((unitSteps 2).card : ℝ) = 4 := by
    rw [card_unitSteps]
    norm_num
  have h1 : ∑ e ∈ unitSteps 2, (f (x + e) - f x) * (f (x + e) - f x) ≤
      ∑ _e ∈ unitSteps 2, M ^ 2 := by
    refine Finset.sum_le_sum fun e he => ?_
    have := hM e he
    calc (f (x + e) - f x) * (f (x + e) - f x) = |f (x + e) - f x| ^ 2 := by
          rw [sq_abs]; ring
      _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at h1
  unfold gammaBr
  have h2 : 0 ≤ (walkOp f x - f x) * (walkOp f x - f x) := mul_self_nonneg _
  have h3 : (1 / (2 * ((2 : ℕ) : ℝ))) * ∑ e ∈ unitSteps 2,
      (f (x + e) - f x) * (f (x + e) - f x) ≤ M ^ 2 := by
    have : (1 / (2 * ((2 : ℕ) : ℝ))) = 1 / 4 := by norm_num
    rw [this]
    linarith
  linarith

/-- A finite sum of a translate of a nonnegative summable weight is at most the total. -/
private theorem pl_sum_translate_le {h : Site 2 → ℝ} (hh : ∀ u, 0 ≤ h u) (hs : Summable h)
    (S : Finset (Site 2)) (y : Site 2) : ∑ x ∈ S, h (x - y) ≤ ∑' u, h u := by
  have hinj : Set.InjOn (fun x : Site 2 => x - y) ↑S := fun a _ b _ hab => sub_left_injective hab
  rw [← Finset.sum_image (f := h) (g := fun x => x - y) hinj]
  exact hs.sum_le_tsum _ (fun u _ => hh u)

/-- The pointwise bound for the weighted bracket of a planar dipole outside the ball of radius
`3k`: with `u = |x - y|`, it is at most `16 K₃² k² (1 + |y|) (1 + u)^{-3}`. -/
private theorem pl_weight_bound {K₃ u0 y0 k g : ℝ} (hu0 : 1 ≤ u0) (hy0 : 0 ≤ y0)
    (hg0 : 0 ≤ g) (hg : g ≤ (K₃ * k / u0 ^ 2) ^ 2) :
    (u0 + y0) * g ≤ 16 * K₃ ^ 2 * k ^ 2 * (1 + y0) * ((1 + u0) ^ 3)⁻¹ := by
  have hu : 0 < u0 := by linarith
  have h1 : u0 + y0 ≤ (1 + u0) * (1 + y0) := by nlinarith [mul_nonneg hu.le hy0]
  have h2 : u0⁻¹ ≤ 2 * (1 + u0)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hu (by linarith)]
    linarith
  have h3 : (u0⁻¹) ^ 4 ≤ (2 * (1 + u0)⁻¹) ^ 4 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hu.le) h2 4
  have hG : (K₃ * k / u0 ^ 2) ^ 2 = K₃ ^ 2 * k ^ 2 * (u0⁻¹) ^ 4 := by
    field_simp
  calc (u0 + y0) * g ≤ ((1 + u0) * (1 + y0)) * (K₃ ^ 2 * k ^ 2 * (u0⁻¹) ^ 4) := by
        rw [← hG]
        exact mul_le_mul h1 hg hg0 (by nlinarith [mul_nonneg hu.le hy0])
    _ ≤ ((1 + u0) * (1 + y0)) * (K₃ ^ 2 * k ^ 2 * (2 * (1 + u0)⁻¹) ^ 4) := by
        refine mul_le_mul_of_nonneg_left ?_ (by nlinarith [mul_nonneg hu.le hy0])
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 16 * K₃ ^ 2 * k ^ 2 * (1 + y0) * ((1 + u0) ^ 3)⁻¹ := by
        have : (1 + u0) ≠ 0 := by linarith
        field_simp
        ring

/-- The weighted partial sums of `Γ` of a planar dipole with itself. -/
private theorem planar_W :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ (y : Site 2) (r : ℝ), 0 ≤ r →
      ∀ S : Finset (Site 2),
      ∑ x ∈ S, min (euclidNorm x) r * gammaBr (dipole y k) (dipole y k) x ≤
        (euclidNorm y + 3 * k) * (2 * (latticeKernel 2 ((k : ℤ) • unit (0 : Fin 2)) +
          latticeKernel 2 (-((k : ℤ) • unit (0 : Fin 2)))) - 2) +
        C * (k : ℝ) ^ 2 * (1 + euclidNorm y) := by
  classical
  obtain ⟨K₃, hK₃, k₀, hD⟩ := pl_dipole_diff
  have hsum3 : Summable fun u : Site 2 => (1 + euclidNorm u) ^ (-(3 : ℝ)) :=
    summable_one_add_euclidNorm_rpow 2 (by norm_num)
  have hpow : ∀ u : Site 2, (1 + euclidNorm u) ^ (-(3 : ℝ)) = ((1 + euclidNorm u) ^ 3)⁻¹ := by
    intro u
    rw [Real.rpow_neg (by linarith [euclidNorm_nonneg u]),
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hnn : ∀ u : Site 2, 0 ≤ (1 + euclidNorm u) ^ (-(3 : ℝ)) := fun u =>
    Real.rpow_nonneg (by linarith [euclidNorm_nonneg u]) _
  set S₃ : ℝ := ∑' u : Site 2, (1 + euclidNorm u) ^ (-(3 : ℝ)) with hS₃
  have hS₃0 : 0 ≤ S₃ := tsum_nonneg hnn
  refine ⟨16 * K₃ ^ 2 * S₃, by positivity, max k₀ 1, fun k hk y r hr S => ?_⟩
  have hkk : k₀ ≤ k := le_trans (le_max_left _ _) hk
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
  have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  set V : ℝ := 2 * (latticeKernel 2 ((k : ℤ) • unit (0 : Fin 2)) +
    latticeKernel 2 (-((k : ℤ) • unit (0 : Fin 2)))) - 2 with hV
  set P : Site 2 → Prop := fun x => euclidNorm (x - y) ≤ 3 * k with hP
  rw [← Finset.sum_filter_add_sum_filter_not S P]
  have hI : ∑ x ∈ S.filter P, min (euclidNorm x) r * gammaBr (dipole y k) (dipole y k) x ≤
      (euclidNorm y + 3 * k) * V := by
    calc _ ≤ ∑ x ∈ S.filter P, (euclidNorm y + 3 * k) *
          gammaBr (dipole y k) (dipole y k) x := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hxP : euclidNorm (x - y) ≤ 3 * k := (Finset.mem_filter.mp hx).2
          have hmin : min (euclidNorm x) r ≤ euclidNorm y + 3 * k := by
            refine (min_le_left _ _).trans ?_
            have h1 := euclidNorm_add_le y (x - y)
            rw [show y + (x - y) = x by abel] at h1
            linarith
          exact mul_le_mul_of_nonneg_right hmin (gammaBr_self_nonneg (by norm_num) _ x)
      _ = (euclidNorm y + 3 * k) * ∑ x ∈ S.filter P, gammaBr (dipole y k) (dipole y k) x := by
          rw [Finset.mul_sum]
      _ ≤ (euclidNorm y + 3 * k) * V :=
          mul_le_mul_of_nonneg_left (planar_V k hk1 y _)
            (by linarith [euclidNorm_nonneg y, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hII : ∑ x ∈ S.filter (fun x => ¬ P x),
      min (euclidNorm x) r * gammaBr (dipole y k) (dipole y k) x ≤
      16 * K₃ ^ 2 * S₃ * (k : ℝ) ^ 2 * (1 + euclidNorm y) := by
    have hpt : ∀ x ∈ S.filter (fun x => ¬ P x),
        min (euclidNorm x) r * gammaBr (dipole y k) (dipole y k) x ≤
        16 * K₃ ^ 2 * (k : ℝ) ^ 2 * (1 + euclidNorm y) * (1 + euclidNorm (x - y)) ^ (-(3 : ℝ)) := by
      intro x hx
      have hxP : 3 * (k : ℝ) < euclidNorm (x - y) := not_le.mp (Finset.mem_filter.mp hx).2
      have hu1 : 1 ≤ euclidNorm (x - y) := by linarith
      have hG := pl_gamma_le_sq (f := dipole y k) (x := x)
        (M := K₃ * k / euclidNorm (x - y) ^ 2) (fun e he => hD k hkk x y e he hxP.le)
      have hG0 := gammaBr_self_nonneg (by norm_num : 1 ≤ 2) (dipole y k) x
      have hxn : euclidNorm x ≤ euclidNorm (x - y) + euclidNorm y := by
        have h1 := euclidNorm_add_le (x - y) y
        rwa [sub_add_cancel] at h1
      have hmin : min (euclidNorm x) r * gammaBr (dipole y k) (dipole y k) x ≤
          (euclidNorm (x - y) + euclidNorm y) * gammaBr (dipole y k) (dipole y k) x :=
        mul_le_mul_of_nonneg_right ((min_le_left _ _).trans hxn) hG0
      rw [hpow]
      exact hmin.trans (pl_weight_bound hu1 (euclidNorm_nonneg y) hG0 hG)
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum]
    have h1 := pl_sum_translate_le (h := fun u => (1 + euclidNorm u) ^ (-(3 : ℝ))) hnn hsum3
      (S.filter (fun x => ¬ P x)) y
    have h2 : 0 ≤ 16 * K₃ ^ 2 * (k : ℝ) ^ 2 * (1 + euclidNorm y) := by
      have := euclidNorm_nonneg y
      positivity
    calc 16 * K₃ ^ 2 * (k : ℝ) ^ 2 * (1 + euclidNorm y) *
          ∑ x ∈ S.filter (fun x => ¬ P x), (1 + euclidNorm (x - y)) ^ (-(3 : ℝ))
        ≤ 16 * K₃ ^ 2 * (k : ℝ) ^ 2 * (1 + euclidNorm y) * S₃ :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = 16 * K₃ ^ 2 * S₃ * (k : ℝ) ^ 2 * (1 + euclidNorm y) := by ring
  linarith

/-! ### The pathwise bracket -/

/-- A simple random walk step has probability `1/(2d)` at every unit step. -/
private theorem srwStep_of_mem {e : Site d} (he : e ∈ unitSteps d) :
    srwStep d e = 1 / (2 * d) := by
  obtain ⟨i, rfl | rfl⟩ := mem_unitSteps.mp he
  · exact srwStep_unit i
  · exact srwStep_neg_unit i

/-- A first-departure probability is within `ε/2` of `1/(2d)` at every unit step. -/
private theorem abs_firstStep_sub_le {ε : ℝ} (hε : 0 ≤ ε) (x : Site d) {e : Site d}
    (he : e ∈ unitSteps d) : |firstStep d ε x e - 1 / (2 * d)| ≤ ε / 2 := by
  have hbound : ∀ i : Fin d, |ε / 2 * (((x i : ℤ) : ℝ) / euclidNorm x)| ≤ ε / 2 := by
    intro i
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ε / 2)]
    calc ε / 2 * |((x i : ℤ) : ℝ) / euclidNorm x| ≤ ε / 2 * 1 :=
          mul_le_mul_of_nonneg_left (abs_coord_div_euclidNorm_le_one x i) (by linarith)
      _ = ε / 2 := mul_one _
  obtain ⟨i, rfl | rfl⟩ := mem_unitSteps.mp he
  · rw [firstStep_unit, sub_sub_cancel_left, abs_neg]
    exact hbound i
  · rw [firstStep_neg_unit, add_sub_cancel_left]
    exact hbound i

/-- The sum of squared one-step increments of `f` at `x`. -/
private noncomputable def incSq (f : Site d → ℝ) (x : Site d) : ℝ :=
  ∑ e ∈ unitSteps d, (f (x + e) - f x) ^ 2

/-- The squared increments have a nonnegative sum. -/
private theorem incSq_nonneg (f : Site d → ℝ) (x : Site d) : 0 ≤ incSq f x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The sum of squared increments is `2d` times the self bracket plus `(Δf)²`. -/
private theorem incSq_eq (hd : 1 ≤ d) (f : Site d → ℝ) (x : Site d) :
    incSq f x = 2 * d * (gammaBr f f x + (walkOp f x - f x) ^ 2) := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [incSq, gammaBr]
  have : ∑ e ∈ unitSteps d, (f (x + e) - f x) ^ 2 =
      ∑ e ∈ unitSteps d, (f (x + e) - f x) * (f (x + e) - f x) :=
    Finset.sum_congr rfl fun e _ => sq _
  rw [this]
  field_simp
  ring

/-- Comparison of the covariance under weights `p` with the uniform covariance. -/
private theorem abs_cov_sub_le (hd : 1 ≤ d) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1 / (d : ℝ))
    (p a b : Site d → ℝ) (hp0 : ∀ e ∈ unitSteps d, 0 ≤ p e)
    (hp1 : ∑ e ∈ unitSteps d, p e = 1)
    (hpu : ∀ e ∈ unitSteps d, |p e - 1 / (2 * d)| ≤ ε / 2) {A B : ℝ} (hA0 : 0 ≤ A)
    (hB0 : 0 ≤ B) (hA : ∀ e ∈ unitSteps d, |a e| ≤ A) (hB : ∀ e ∈ unitSteps d, |b e| ≤ B) :
    |(∑ e ∈ unitSteps d, p e * (a e * b e) -
        (∑ e ∈ unitSteps d, p e * a e) * (∑ e ∈ unitSteps d, p e * b e)) -
      ((1 / (2 * d)) * ∑ e ∈ unitSteps d, a e * b e -
        ((1 / (2 * d)) * ∑ e ∈ unitSteps d, a e) *
          ((1 / (2 * d)) * ∑ e ∈ unitSteps d, b e))| ≤ 3 * (A * B) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdε : (d : ℝ) * ε ≤ 1 := by
    have := (lt_div_iff₀ hd').mp hε1
    nlinarith
  have hN : ((unitSteps d).card : ℝ) = 2 * d := by rw [card_unitSteps]; push_cast; ring
  set u : ℝ := 1 / (2 * d) with hu
  have hu0 : 0 ≤ u := by positivity
  have hdu : (2 * (d : ℝ)) * u = 1 := by rw [hu]; field_simp
  have hsum_dε : ∀ M : ℝ, 0 ≤ M → ∑ _e ∈ unitSteps d, (ε / 2) * M ≤ M := by
    intro M hM
    rw [Finset.sum_const, nsmul_eq_mul, hN]
    calc (2 * (d : ℝ)) * (ε / 2 * M) = ((d : ℝ) * ε) * M := by ring
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right hdε hM
      _ = M := one_mul _
  have hT1 : |∑ e ∈ unitSteps d, (p e - u) * (a e * b e)| ≤ A * B := by
    calc _ ≤ ∑ e ∈ unitSteps d, |(p e - u) * (a e * b e)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ unitSteps d, (ε / 2) * (A * B) := by
          refine Finset.sum_le_sum fun e he => ?_
          rw [abs_mul, abs_mul]
          exact mul_le_mul (hpu e he) (mul_le_mul (hA e he) (hB e he) (abs_nonneg _) hA0)
            (by positivity) (by linarith)
      _ ≤ A * B := hsum_dε _ (mul_nonneg hA0 hB0)
  have hSa : |∑ e ∈ unitSteps d, (p e - u) * a e| ≤ A := by
    calc _ ≤ ∑ e ∈ unitSteps d, |(p e - u) * a e| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ unitSteps d, (ε / 2) * A := by
          refine Finset.sum_le_sum fun e he => ?_
          rw [abs_mul]
          exact mul_le_mul (hpu e he) (hA e he) (abs_nonneg _) (by linarith)
      _ ≤ A := hsum_dε _ hA0
  have hSb : |∑ e ∈ unitSteps d, (p e - u) * b e| ≤ B := by
    calc _ ≤ ∑ e ∈ unitSteps d, |(p e - u) * b e| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ unitSteps d, (ε / 2) * B := by
          refine Finset.sum_le_sum fun e he => ?_
          rw [abs_mul]
          exact mul_le_mul (hpu e he) (hB e he) (abs_nonneg _) (by linarith)
      _ ≤ B := hsum_dε _ hB0
  have hPb : |∑ e ∈ unitSteps d, p e * b e| ≤ B := by
    calc _ ≤ ∑ e ∈ unitSteps d, |p e * b e| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ unitSteps d, p e * B := by
          refine Finset.sum_le_sum fun e he => ?_
          rw [abs_mul, abs_of_nonneg (hp0 e he)]
          exact mul_le_mul_of_nonneg_left (hB e he) (hp0 e he)
      _ = B := by rw [← Finset.sum_mul, hp1, one_mul]
  have hUa : |∑ e ∈ unitSteps d, u * a e| ≤ A := by
    calc _ ≤ ∑ e ∈ unitSteps d, |u * a e| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ unitSteps d, u * A := by
          refine Finset.sum_le_sum fun e he => ?_
          rw [abs_mul, abs_of_nonneg hu0]
          exact mul_le_mul_of_nonneg_left (hA e he) hu0
      _ = A := by rw [Finset.sum_const, nsmul_eq_mul, hN]; linear_combination A * hdu
  have hid : (∑ e ∈ unitSteps d, p e * (a e * b e) -
        (∑ e ∈ unitSteps d, p e * a e) * (∑ e ∈ unitSteps d, p e * b e)) -
      ((1 / (2 * d)) * ∑ e ∈ unitSteps d, a e * b e -
        ((1 / (2 * d)) * ∑ e ∈ unitSteps d, a e) *
          ((1 / (2 * d)) * ∑ e ∈ unitSteps d, b e)) =
      ∑ e ∈ unitSteps d, (p e - u) * (a e * b e) -
        ((∑ e ∈ unitSteps d, (p e - u) * a e) * (∑ e ∈ unitSteps d, p e * b e) +
          (∑ e ∈ unitSteps d, u * a e) * (∑ e ∈ unitSteps d, (p e - u) * b e)) := by
    have e1 : ∑ e ∈ unitSteps d, (p e - u) * (a e * b e) =
        ∑ e ∈ unitSteps d, p e * (a e * b e) - u * ∑ e ∈ unitSteps d, a e * b e := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun e _ => by ring
    have e2 : ∑ e ∈ unitSteps d, (p e - u) * a e =
        ∑ e ∈ unitSteps d, p e * a e - u * ∑ e ∈ unitSteps d, a e := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun e _ => by ring
    have e3 : ∑ e ∈ unitSteps d, (p e - u) * b e =
        ∑ e ∈ unitSteps d, p e * b e - u * ∑ e ∈ unitSteps d, b e := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun e _ => by ring
    have e4 : ∑ e ∈ unitSteps d, u * a e = u * ∑ e ∈ unitSteps d, a e := by
      rw [Finset.mul_sum]
    rw [e1, e2, e3, e4]
    ring
  rw [hid]
  have h2 : |(∑ e ∈ unitSteps d, (p e - u) * a e) * (∑ e ∈ unitSteps d, p e * b e) +
      (∑ e ∈ unitSteps d, u * a e) * (∑ e ∈ unitSteps d, (p e - u) * b e)| ≤ 2 * (A * B) := by
    calc _ ≤ |(∑ e ∈ unitSteps d, (p e - u) * a e) * (∑ e ∈ unitSteps d, p e * b e)| +
          |(∑ e ∈ unitSteps d, u * a e) * (∑ e ∈ unitSteps d, (p e - u) * b e)| :=
          abs_add_le _ _
      _ ≤ A * B + A * B := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul hSa hPb (abs_nonneg _) hA0)
            (mul_le_mul hUa hSb (abs_nonneg _) hA0)
      _ = 2 * (A * B) := by ring
  calc _ ≤ |∑ e ∈ unitSteps d, (p e - u) * (a e * b e)| +
        |(∑ e ∈ unitSteps d, (p e - u) * a e) * (∑ e ∈ unitSteps d, p e * b e) +
        (∑ e ∈ unitSteps d, u * a e) * (∑ e ∈ unitSteps d, (p e - u) * b e)| := abs_sub _ _
    _ ≤ A * B + 2 * (A * B) := add_le_add hT1 h2
    _ = 3 * (A * B) := by ring


/-- At one time, the conditional covariance of the increments of `f` and `g` under the step
law differs from the pointwise bracket by at most `(3/2)` of the squared increments, and only
at a first departure from a nonzero site. -/
private theorem abs_step_cov_sub_le (hd : 1 ≤ d) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1 / (d : ℝ))
    (Y : ℕ → Site d) (t : ℕ) (f g : Site d → ℝ) :
    |(∑ e ∈ unitSteps d, stepProb d ε Y t e *
          ((f (Y t + e) - f (Y t)) * (g (Y t + e) - g (Y t))) -
        stepMean (stepProb d ε) f Y t * stepMean (stepProb d ε) g Y t) - gammaBr f g (Y t)| ≤
      if Y t ≠ 0 ∧ Y t ∉ (Finset.range t).image Y then
        3 / 2 * (incSq f (Y t) + incSq g (Y t)) else 0 := by
  have hcov : ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → (∀ e ∈ unitSteps d, |f (Y t + e) - f (Y t)| ≤ A) →
      (∀ e ∈ unitSteps d, |g (Y t + e) - g (Y t)| ≤ B) →
      |(∑ e ∈ unitSteps d, stepProb d ε Y t e *
          ((f (Y t + e) - f (Y t)) * (g (Y t + e) - g (Y t))) -
        stepMean (stepProb d ε) f Y t * stepMean (stepProb d ε) g Y t) - gammaBr f g (Y t)| ≤
        3 * (A * B) := by
    intro A B hA0 hB0 hA hB
    rw [gammaBr_eq_cov hd]
    have hpu : ∀ e ∈ unitSteps d, |stepProb d ε Y t e - 1 / (2 * d)| ≤ ε / 2 := by
      intro e he
      unfold stepProb
      split_ifs with h
      · exact abs_firstStep_sub_le hε0 _ he
      · rw [srwStep_of_mem he, sub_self, abs_zero]
        linarith
    exact abs_cov_sub_le hd hε0 hε1 (stepProb d ε Y t) (fun e => f (Y t + e) - f (Y t))
      (fun e => g (Y t + e) - g (Y t)) (fun e _ => stepProb_nonneg hε0 hε1 Y t e)
      (sum_stepProb hd ε Y t) hpu hA0 hB0 hA hB
  by_cases hfresh : Y t ≠ 0 ∧ Y t ∉ (Finset.range t).image Y
  · rw [if_pos hfresh]
    have hA : ∀ e ∈ unitSteps d, |f (Y t + e) - f (Y t)| ≤ Real.sqrt (incSq f (Y t)) := by
      intro e he
      refine Real.abs_le_sqrt ?_
      exact Finset.single_le_sum (f := fun e => (f (Y t + e) - f (Y t)) ^ 2)
        (fun _ _ => sq_nonneg _) he
    have hB : ∀ e ∈ unitSteps d, |g (Y t + e) - g (Y t)| ≤ Real.sqrt (incSq g (Y t)) := by
      intro e he
      refine Real.abs_le_sqrt ?_
      exact Finset.single_le_sum (f := fun e => (g (Y t + e) - g (Y t)) ^ 2)
        (fun _ _ => sq_nonneg _) he
    refine (hcov _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hA hB).trans ?_
    have h1 := Real.sq_sqrt (incSq_nonneg f (Y t))
    have h2 := Real.sq_sqrt (incSq_nonneg g (Y t))
    nlinarith [sq_nonneg (Real.sqrt (incSq f (Y t)) - Real.sqrt (incSq g (Y t)))]
  · rw [if_neg hfresh]
    have hp : ∀ e ∈ unitSteps d, stepProb d ε Y t e = 1 / (2 * d) := fun e he => by
      rw [stepProb, if_neg hfresh, srwStep_of_mem he]
    have hmean : ∀ h : Site d → ℝ, stepMean (stepProb d ε) h Y t =
        (1 / (2 * d)) * ∑ e ∈ unitSteps d, (h (Y t + e) - h (Y t)) := by
      intro h
      rw [stepMean, Finset.mul_sum]
      exact Finset.sum_congr rfl fun e he => by rw [hp e he]
    have hcross : ∑ e ∈ unitSteps d, stepProb d ε Y t e *
          ((f (Y t + e) - f (Y t)) * (g (Y t + e) - g (Y t))) =
        (1 / (2 * d)) * ∑ e ∈ unitSteps d, (f (Y t + e) - f (Y t)) * (g (Y t + e) - g (Y t)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e he => by rw [hp e he]
    rw [gammaBr_eq_cov hd, hcross, hmean f, hmean g, sub_self, abs_zero]

/-- The pathwise bracket of the Dynkin martingales of `f` and `g` is the local-time weighted
sum of the pointwise bracket, up to `(3/2)` of the squared increments over the range. -/
private theorem abs_dynkinBracket_sub_le (hd : 1 ≤ d) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1 / (d : ℝ)) (f g : Site d → ℝ) (Y : ℕ → Site d) (n : ℕ) :
    |dynkinBracket (stepProb d ε) f g Y n -
        ∑ z ∈ departureRange Y n, (localTime Y n z : ℝ) * gammaBr f g z| ≤
      3 / 2 * ∑ z ∈ departureRange Y n, (incSq f z + incSq g z) := by
  rw [← sum_range_eq_sum_localTime Y n (gammaBr f g), dynkinBracket, ← Finset.sum_sub_distrib]
  calc |∑ t ∈ Finset.range n, ((∑ e ∈ unitSteps d, stepProb d ε Y t e *
            ((f (Y t + e) - f (Y t)) * (g (Y t + e) - g (Y t))) -
          stepMean (stepProb d ε) f Y t * stepMean (stepProb d ε) g Y t) - gammaBr f g (Y t))|
      ≤ ∑ t ∈ Finset.range n, |(∑ e ∈ unitSteps d, stepProb d ε Y t e *
            ((f (Y t + e) - f (Y t)) * (g (Y t + e) - g (Y t))) -
          stepMean (stepProb d ε) f Y t * stepMean (stepProb d ε) g Y t) - gammaBr f g (Y t)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range n, (if Y t ≠ 0 ∧ Y t ∉ (Finset.range t).image Y then
          3 / 2 * (incSq f (Y t) + incSq g (Y t)) else 0) :=
        Finset.sum_le_sum fun t _ => abs_step_cov_sub_le hd hε0 hε1 Y t f g
    _ = 3 / 2 * ∑ z ∈ departureRange Y n,
          (if z ≠ 0 then incSq f z + incSq g z else 0) := by
        rw [Finset.mul_sum]
        have := sum_fresh_ne_zero_eq_sum_departureRange Y n (fun z => 3 / 2 *
          (incSq f z + incSq g z))
        rw [this]
        refine Finset.sum_congr rfl fun z _ => ?_
        split_ifs <;> simp
    _ ≤ 3 / 2 * ∑ z ∈ departureRange Y n, (incSq f z + incSq g z) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => ?_) (by norm_num)
        split_ifs
        · exact le_rfl
        · exact add_nonneg (incSq_nonneg f z) (incSq_nonneg g z)

/-- The positive part of the profile is the radius minus the truncated norm. -/
private theorem max_sub_eq (r a : ℝ) : max (r - a) 0 = r - min a r := by
  rcases le_total a r with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
  · rw [min_eq_right h, max_eq_right (by linarith)]
    ring

/-- Replacing the local time by its profile: the local-time weighted sum of `Γ` is
`2 d ε r Σ Γ` up to `err Σ|Γ| + 2dε Σ min(|x|, r) |Γ|`. -/
private theorem abs_profile_sum_sub_le {ε : ℝ} (hε0 : 0 ≤ ε) (Y : ℕ → Site d) (n : ℕ)
    (r err M₁ M₂ : ℝ) (hr : 0 ≤ r)
    (hprof : ∀ x : Site d,
      |(localTime Y n x : ℝ) - 2 * d * ε * max (r - euclidNorm x) 0| ≤ err)
    (Γ : Site d → ℝ) (hΓ₁ : ∀ S : Finset (Site d), ∑ x ∈ S, |Γ x| ≤ M₁)
    (hΓ₂ : ∀ S : Finset (Site d), ∑ x ∈ S, min (euclidNorm x) r * |Γ x| ≤ M₂) :
    |∑ z ∈ departureRange Y n, (localTime Y n z : ℝ) * Γ z - 2 * d * ε * r * ∑' x, Γ x| ≤
      err * M₁ + 2 * d * ε * M₂ := by
  set c : ℝ := 2 * d * ε with hc
  have hc0 : 0 ≤ c := by positivity
  have hmin0 : ∀ x : Site d, 0 ≤ min (euclidNorm x) r := fun x =>
    le_min (euclidNorm_nonneg x) hr
  have hs1 : Summable (fun x => |Γ x|) := summable_of_sum_le (fun x => abs_nonneg _) hΓ₁
  have hs0 : Summable Γ := hs1.of_abs
  have hs2 : Summable (fun x => min (euclidNorm x) r * |Γ x|) :=
    summable_of_sum_le (fun x => mul_nonneg (hmin0 x) (abs_nonneg _)) hΓ₂
  have ht1 : ∑' x, |Γ x| ≤ M₁ := hs1.tsum_le_of_sum_le hΓ₁
  have ht2 : ∑' x, min (euclidNorm x) r * |Γ x| ≤ M₂ := hs2.tsum_le_of_sum_le hΓ₂
  have hsupp : ∀ x ∉ departureRange Y n, (localTime Y n x : ℝ) * Γ x = 0 := by
    intro x hx
    rw [mem_departureRange_iff, not_lt, Nat.le_zero] at hx
    rw [hx]
    simp
  have heq : ∑ z ∈ departureRange Y n, (localTime Y n z : ℝ) * Γ z =
      ∑' x, (localTime Y n x : ℝ) * Γ x := (tsum_eq_sum hsupp).symm
  have hsl : Summable (fun x => (localTime Y n x : ℝ) * Γ x) := summable_of_ne_finset_zero hsupp
  have hlin : ∑' x, (localTime Y n x : ℝ) * Γ x - c * r * ∑' x, Γ x =
      ∑' x, ((localTime Y n x : ℝ) * Γ x - c * r * Γ x) := by
    rw [hsl.tsum_sub (hs0.mul_left _), tsum_mul_left]
  have hg : Summable (fun x => (localTime Y n x : ℝ) * Γ x - c * r * Γ x) :=
    hsl.sub (hs0.mul_left _)
  have hpt : ∀ x, |(localTime Y n x : ℝ) * Γ x - c * r * Γ x| ≤
      err * |Γ x| + c * (min (euclidNorm x) r * |Γ x|) := by
    intro x
    have h1 : |(localTime Y n x : ℝ) - c * r| ≤ err + c * min (euclidNorm x) r := by
      have h2 : (localTime Y n x : ℝ) - c * r =
          ((localTime Y n x : ℝ) - c * max (r - euclidNorm x) 0) +
            (-(c * min (euclidNorm x) r)) := by
        rw [max_sub_eq]
        ring
      rw [h2]
      refine (abs_add_le _ _).trans (add_le_add (hprof x) ?_)
      rw [abs_neg, abs_of_nonneg (mul_nonneg hc0 (hmin0 x))]
    calc |(localTime Y n x : ℝ) * Γ x - c * r * Γ x|
        = |(localTime Y n x : ℝ) - c * r| * |Γ x| := by rw [← abs_mul]; ring_nf
      _ ≤ (err + c * min (euclidNorm x) r) * |Γ x| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = err * |Γ x| + c * (min (euclidNorm x) r * |Γ x|) := by ring
  rw [heq, hlin]
  calc |∑' x, ((localTime Y n x : ℝ) * Γ x - c * r * Γ x)|
      ≤ ∑' x, |(localTime Y n x : ℝ) * Γ x - c * r * Γ x| := by
        have := norm_tsum_le_tsum_norm hg.norm
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' x, (err * |Γ x| + c * (min (euclidNorm x) r * |Γ x|)) :=
        hg.abs.tsum_le_tsum hpt ((hs1.mul_left err).add (hs2.mul_left c))
    _ = err * ∑' x, |Γ x| + c * ∑' x, min (euclidNorm x) r * |Γ x| := by
        rw [(hs1.mul_left err).tsum_add (hs2.mul_left c), tsum_mul_left, tsum_mul_left]
    _ ≤ err * M₁ + c * M₂ := by
        have herr : 0 ≤ err := (abs_nonneg _).trans (hprof 0)
        exact add_le_add (mul_le_mul_of_nonneg_left ht1 herr) (mul_le_mul_of_nonneg_left ht2 hc0)

/-- **The bracket against the profile.** The pathwise bracket of `F` and `G` is
`2 d ε r Σ_x Γ(F, G)(x)` up to an error controlled by the partial-sum bounds `V`, `W`, `D`
of the self brackets and of the Laplacians, and the local-time profile error `err`. -/
private theorem bracket_approx (hd : 1 ≤ d) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1 / (d : ℝ))
    (Y : ℕ → Site d) (n : ℕ) (r err V W D : ℝ) (hr : 0 ≤ r)
    (hprof : ∀ x : Site d,
      |(localTime Y n x : ℝ) - 2 * d * ε * max (r - euclidNorm x) 0| ≤ err)
    (F G : Site d → ℝ)
    (hVF : ∀ S : Finset (Site d), ∑ x ∈ S, gammaBr F F x ≤ V)
    (hVG : ∀ S : Finset (Site d), ∑ x ∈ S, gammaBr G G x ≤ V)
    (hWF : ∀ S : Finset (Site d), ∑ x ∈ S, min (euclidNorm x) r * gammaBr F F x ≤ W)
    (hWG : ∀ S : Finset (Site d), ∑ x ∈ S, min (euclidNorm x) r * gammaBr G G x ≤ W)
    (hDF : ∀ S : Finset (Site d), ∑ x ∈ S, (walkOp F x - F x) ^ 2 ≤ D)
    (hDG : ∀ S : Finset (Site d), ∑ x ∈ S, (walkOp G x - G x) ^ 2 ≤ D) :
    |dynkinBracket (stepProb d ε) F G Y n - 2 * d * ε * r * ∑' x, gammaBr F G x| ≤
      6 * d * (V + D) + err * V + 2 * d * ε * W := by
  have hmin0 : ∀ x : Site d, 0 ≤ min (euclidNorm x) r := fun x =>
    le_min (euclidNorm_nonneg x) hr
  set A := departureRange Y n with hA
  have h1 := abs_dynkinBracket_sub_le hd hε0 hε1 F G Y n
  have hQ : ∀ H : Site d → ℝ, ∑ z ∈ A, incSq H z =
      2 * d * (∑ z ∈ A, gammaBr H H z + ∑ z ∈ A, (walkOp H z - H z) ^ 2) := by
    intro H
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => incSq_eq hd H z
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hQF : ∑ z ∈ A, incSq F z ≤ 2 * d * (V + D) := by
    rw [hQ F]
    exact mul_le_mul_of_nonneg_left (add_le_add (hVF A) (hDF A)) (by positivity)
  have hQG : ∑ z ∈ A, incSq G z ≤ 2 * d * (V + D) := by
    rw [hQ G]
    exact mul_le_mul_of_nonneg_left (add_le_add (hVG A) (hDG A)) (by positivity)
  have hE1 : |dynkinBracket (stepProb d ε) F G Y n -
        ∑ z ∈ A, (localTime Y n z : ℝ) * gammaBr F G z| ≤ 6 * d * (V + D) := by
    refine h1.trans ?_
    rw [Finset.sum_add_distrib]
    nlinarith [hQF, hQG]
  have hΓ₁ : ∀ S : Finset (Site d), ∑ x ∈ S, |gammaBr F G x| ≤ V := by
    intro S
    calc ∑ x ∈ S, |gammaBr F G x| ≤ ∑ x ∈ S, (gammaBr F F x + gammaBr G G x) / 2 :=
          Finset.sum_le_sum fun x _ => abs_gammaBr_le hd F G x
      _ = (∑ x ∈ S, gammaBr F F x + ∑ x ∈ S, gammaBr G G x) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
      _ ≤ V := by linarith [hVF S, hVG S]
  have hΓ₂ : ∀ S : Finset (Site d), ∑ x ∈ S, min (euclidNorm x) r * |gammaBr F G x| ≤ W := by
    intro S
    calc ∑ x ∈ S, min (euclidNorm x) r * |gammaBr F G x|
        ≤ ∑ x ∈ S, (min (euclidNorm x) r * gammaBr F F x +
            min (euclidNorm x) r * gammaBr G G x) / 2 := by
          refine Finset.sum_le_sum fun x _ => ?_
          have := mul_le_mul_of_nonneg_left (abs_gammaBr_le hd F G x) (hmin0 x)
          linarith
      _ = (∑ x ∈ S, min (euclidNorm x) r * gammaBr F F x +
            ∑ x ∈ S, min (euclidNorm x) r * gammaBr G G x) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
      _ ≤ W := by linarith [hWF S, hWG S]
  have h2 := abs_profile_sum_sub_le hε0 Y n r err V W hr hprof (gammaBr F G) hΓ₁ hΓ₂
  calc |dynkinBracket (stepProb d ε) F G Y n - 2 * d * ε * r * ∑' x, gammaBr F G x|
      = |(dynkinBracket (stepProb d ε) F G Y n -
            ∑ z ∈ A, (localTime Y n z : ℝ) * gammaBr F G z) +
          (∑ z ∈ A, (localTime Y n z : ℝ) * gammaBr F G z -
            2 * d * ε * r * ∑' x, gammaBr F G x)| := by ring_nf
    _ ≤ 6 * d * (V + D) + (err * V + 2 * d * ε * W) := (abs_add_le _ _).trans (add_le_add hE1 h2)
    _ = 6 * d * (V + D) + err * V + 2 * d * ε * W := by ring


/-- **The pair estimate for `d ≥ 3`.** For two translates of the kernel centred at `y`, `y'`
of norm at most `2 t³`, the normalized pathwise bracket is `2 d ε` times the total of `Γ` up
to `C₁ / t²`, when the local times follow the profile `2dε (t⁸ - |x|)₊` within `P t⁶`. -/
private theorem high_pair (hd : 3 ≤ d) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / (d : ℝ)) {P : ℝ}
    (hP : 0 ≤ P) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (t : ℝ) (n : ℕ) (Y : ℕ → Site d) (y y' : Site d) (err : ℝ),
      1 ≤ t → euclidNorm y ≤ 2 * t ^ 3 → euclidNorm y' ≤ 2 * t ^ 3 → err ≤ P * t ^ 6 →
      (∀ x : Site d,
        |(localTime Y n x : ℝ) - 2 * d * ε * max (t ^ 8 - euclidNorm x) 0| ≤ err) →
      |dynkinBracket (stepProb d ε) (fun z => latticeKernel d (z - y))
          (fun z => latticeKernel d (z - y')) Y n / t ^ 8 -
        2 * d * ε * ∑' x, gammaBr (fun z => latticeKernel d (z - y))
          (fun z => latticeKernel d (z - y')) x| ≤ C₁ / t ^ 2 := by
  obtain ⟨CW, hCW0, hW⟩ := high_W hd
  have hG0 : 1 ≤ srwGreenInf d (0 : Site d) := one_le_srwGreenInf_origin hd
  set V : ℝ := 2 * srwGreenInf d 0 - 1 with hV
  have hV1 : 1 ≤ V := by rw [hV]; linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨6 * d * (V + 1) + P * V + 6 * d * ε * CW, by positivity, ?_⟩
  intro t n Y y y' err ht hy hy' herr hprof
  have ht0 : 0 < t := by linarith
  have ht8 : (0 : ℝ) ≤ t ^ 8 := by positivity
  have hsq : Real.sqrt (t ^ 8) = t ^ 4 := by
    rw [show t ^ 8 = (t ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hsy : ∀ z : Site d, euclidNorm z ≤ 2 * t ^ 3 → Real.sqrt (euclidNorm z) ≤ 2 * t ^ 2 := by
    intro z hz
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h3 : t ^ 3 ≤ t ^ 4 := pow_le_pow_right₀ ht (by norm_num)
    nlinarith
  have hWS : ∀ z : Site d, euclidNorm z ≤ 2 * t ^ 3 → ∀ S : Finset (Site d),
      ∑ x ∈ S, min (euclidNorm x) (t ^ 8) *
          gammaBr (fun w => latticeKernel d (w - z)) (fun w => latticeKernel d (w - z)) x ≤
        CW * t ^ 4 * (1 + 2 * t ^ 2) := by
    intro z hz S
    refine (hW z (t ^ 8) ht8 S).trans ?_
    rw [hsq]
    have := hsy z hz
    calc CW * t ^ 4 * (1 + Real.sqrt (euclidNorm z)) ≤ CW * t ^ 4 * (1 + 2 * t ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ = CW * t ^ 4 * (1 + 2 * t ^ 2) := rfl
  have hmain := bracket_approx (d := d) (by omega) hε0.le hε1 Y n (t ^ 8) err V
    (CW * t ^ 4 * (1 + 2 * t ^ 2)) 1 ht8 hprof (fun z => latticeKernel d (z - y))
    (fun z => latticeKernel d (z - y')) (high_V hd y) (high_V hd y') (hWS y hy) (hWS y' hy')
    (kernel_translate_D (by omega) y) (kernel_translate_D (by omega) y')
  have ht6 : (1 : ℝ) ≤ t ^ 6 := one_le_pow₀ ht
  have hE : 6 * d * (V + 1) + err * V + 2 * d * ε * (CW * t ^ 4 * (1 + 2 * t ^ 2)) ≤
      (6 * d * (V + 1) + P * V + 6 * d * ε * CW) * t ^ 6 := by
    have h1 : 6 * (d : ℝ) * (V + 1) ≤ 6 * d * (V + 1) * t ^ 6 := by
      have : (0 : ℝ) ≤ 6 * d * (V + 1) := by positivity
      nlinarith
    have h2 : err * V ≤ P * V * t ^ 6 := by
      have := mul_le_mul_of_nonneg_right herr (by linarith : (0 : ℝ) ≤ V)
      linarith
    have h3 : 2 * (d : ℝ) * ε * (CW * t ^ 4 * (1 + 2 * t ^ 2)) ≤ 6 * d * ε * CW * t ^ 6 := by
      have h4 : t ^ 4 * (1 + 2 * t ^ 2) ≤ 3 * t ^ 6 := by
        have : t ^ 4 ≤ t ^ 6 := pow_le_pow_right₀ ht (by norm_num)
        nlinarith
      have h5 : 0 ≤ 2 * (d : ℝ) * ε * CW := by positivity
      calc 2 * (d : ℝ) * ε * (CW * t ^ 4 * (1 + 2 * t ^ 2))
          = (2 * d * ε * CW) * (t ^ 4 * (1 + 2 * t ^ 2)) := by ring
        _ ≤ (2 * d * ε * CW) * (3 * t ^ 6) := mul_le_mul_of_nonneg_left h4 h5
        _ = 6 * d * ε * CW * t ^ 6 := by ring
    nlinarith
  have hkey := hmain.trans hE
  have heq : dynkinBracket (stepProb d ε) (fun z => latticeKernel d (z - y))
        (fun z => latticeKernel d (z - y')) Y n / t ^ 8 -
      2 * d * ε * ∑' x, gammaBr (fun z => latticeKernel d (z - y))
        (fun z => latticeKernel d (z - y')) x =
      (dynkinBracket (stepProb d ε) (fun z => latticeKernel d (z - y))
        (fun z => latticeKernel d (z - y')) Y n - 2 * d * ε * t ^ 8 *
        ∑' x, gammaBr (fun z => latticeKernel d (z - y))
          (fun z => latticeKernel d (z - y')) x) / t ^ 8 := by
    field_simp
  rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 8)]
  calc _ ≤ (6 * d * (V + 1) + P * V + 6 * d * ε * CW) * t ^ 6 / t ^ 8 :=
        div_le_div_of_nonneg_right hkey (by positivity)
    _ = (6 * d * (V + 1) + P * V + 6 * d * ε * CW) / t ^ 2 := by
        field_simp

/-- The positions `i Yc` and `j Yc` of the axis, `i ≠ j`, differ by at least `Yc`. -/
private theorem axis_sep_abs (Yc : ℕ) {i j : ℕ} (hij : i ≠ j) :
    (Yc : ℝ) ≤ |((((i * Yc : ℕ) : ℤ) - ((j * Yc : ℕ) : ℤ) : ℤ) : ℝ)| := by
  have h1 : (((i * Yc : ℕ) : ℤ) - ((j * Yc : ℕ) : ℤ) : ℤ) = ((i : ℤ) - j) * Yc := by
    push_cast
    ring
  rw [h1]
  have h2 : (1 : ℤ) ≤ |(i : ℤ) - j| := Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast hij))
  have h3 : (1 : ℝ) ≤ |((i : ℝ) - j)| := by exact_mod_cast h2
  push_cast
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg Yc : (0 : ℝ) ≤ Yc)]
  nlinarith [Nat.cast_nonneg (α := ℝ) Yc]

/-- Two sites of the axis, at positions `i Yc` and `j Yc` with `i ≠ j`, are at distance at
least `Yc`. -/
private theorem axis_dist (i₀ : Fin d) (Yc : ℕ) {i j : ℕ} (hij : i ≠ j) :
    (Yc : ℝ) ≤ euclidNorm (((i * Yc : ℕ) : ℤ) • unit i₀ - ((j * Yc : ℕ) : ℤ) • unit i₀) := by
  rw [← sub_smul, pl_norm_smul_unit]
  exact axis_sep_abs Yc hij

/-- The site at position `i Yc` of the axis has norm `i Yc`. -/
private theorem axis_norm (i₀ : Fin d) (i Yc : ℕ) :
    euclidNorm (((i * Yc : ℕ) : ℤ) • unit i₀) = (i : ℝ) * Yc := by
  rw [pl_norm_smul_unit]
  push_cast
  rw [abs_of_nonneg (by positivity)]

/-- **The brackets for `d ≥ 3`**: for large `t`, the normalized diagonal brackets lie between
two positive constants and the off-diagonal ones are at most `C / t²`. -/
private theorem assembly_high (hd : 3 ≤ d) (i₀ : Fin d) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1 / (d : ℝ)) {P : ℝ} (hP : 0 ≤ P) :
    ∃ t₀ c₀ C₀ C : ℝ, 1 ≤ t₀ ∧ 0 < c₀ ∧ c₀ ≤ C₀ ∧ 0 < C ∧
      ∀ (t : ℝ) (Yc m n : ℕ) (Y : ℕ → Site d) (err : ℝ), t₀ ≤ t → t ^ 2 ≤ Yc →
        (Yc : ℝ) ≤ 2 * t ^ 2 → (m : ℝ) ≤ t → err ≤ P * t ^ 6 →
        (∀ x : Site d,
          |(localTime Y n x : ℝ) - 2 * d * ε * max (t ^ 8 - euclidNorm x) 0| ≤ err) →
        ∀ i j : ℕ, 1 ≤ i → i ≤ m → 1 ≤ j → j ≤ m → ∀ B : ℝ,
          B = dynkinBracket (stepProb d ε)
            (fun z => latticeKernel d (z - ((i * Yc : ℕ) : ℤ) • unit i₀))
            (fun z => latticeKernel d (z - ((j * Yc : ℕ) : ℤ) • unit i₀)) Y n / t ^ 8 →
          (i = j → c₀ ≤ B ∧ B ≤ C₀) ∧ (i ≠ j → |B| ≤ C / t ^ 2) := by
  obtain ⟨C₁, hC₁0, hpair⟩ := high_pair hd hε0 hε1 hP
  obtain ⟨K, hK0, hK⟩ := green_decay hd
  have hG0 : 1 ≤ srwGreenInf d (0 : Site d) := one_le_srwGreenInf_origin hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdε : 0 < (d : ℝ) * ε := mul_pos hd0 hε0
  set Tii : ℝ := 2 * srwGreenInf d 0 - 1 with hTii
  have hT1 : 1 ≤ Tii := by rw [hTii]; linarith
  refine ⟨max 1 (C₁ / (d * ε) + C₁ + 1), d * ε, 2 * d * ε * Tii + 1, 4 * d * ε * K + C₁ + 1,
    le_max_left _ _, hdε, ?_, by positivity, ?_⟩
  · nlinarith
  intro t Yc m n Y err ht hY1 hY2 hm herr hprof i j hi1 him hj1 hjm B hB
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have ht0 : 0 < t := by linarith
  have hYc1 : 1 ≤ Yc := by
    have : (1 : ℝ) ≤ Yc := le_trans (by nlinarith) hY1
    exact_mod_cast this
  have hnorm : ∀ i : ℕ, 1 ≤ i → i ≤ m →
      euclidNorm (((i * Yc : ℕ) : ℤ) • unit i₀) ≤ 2 * t ^ 3 := by
    intro i hi1 him
    rw [axis_norm]
    have h1 : (i : ℝ) ≤ t := le_trans (by exact_mod_cast him) hm
    calc (i : ℝ) * Yc ≤ t * (2 * t ^ 2) :=
          mul_le_mul h1 hY2 (Nat.cast_nonneg Yc) ht0.le
      _ = 2 * t ^ 3 := by ring
  have hpair' := hpair t n Y _ _ err ht1 (hnorm i hi1 him) (hnorm j hj1 hjm) herr hprof
  rw [← hB] at hpair'
  have hsmall1 : C₁ / t ^ 2 ≤ d * ε := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : C₁ / (d * ε) ≤ t :=
      le_trans (le_max_of_le_right (by linarith [hC₁0])) ht
    rw [div_le_iff₀ hdε] at h1
    nlinarith
  have hsmall2 : C₁ / t ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    have h1 : C₁ + 1 ≤ t :=
      le_trans (le_max_of_le_right (by linarith [div_nonneg hC₁0 hdε.le])) ht
    nlinarith
  constructor
  · rintro rfl
    have hval := (high_tsum hd (((i * Yc : ℕ) : ℤ) • unit i₀) (((i * Yc : ℕ) : ℤ) • unit i₀)).2
    rw [if_pos rfl] at hval
    rw [hval] at hpair'
    have h2 := abs_le.mp hpair'
    constructor
    · nlinarith
    · nlinarith
  · intro hij
    have hne : (((i * Yc : ℕ) : ℤ) • unit i₀) ≠ (((j * Yc : ℕ) : ℤ) • unit i₀) := by
      intro h
      have := axis_dist i₀ Yc hij
      rw [h, sub_self, euclidNorm_zero] at this
      have : (1 : ℝ) ≤ Yc := by exact_mod_cast hYc1
      linarith
    have hval := (high_tsum hd (((i * Yc : ℕ) : ℤ) • unit i₀) (((j * Yc : ℕ) : ℤ) • unit i₀)).2
    rw [if_neg hne] at hval
    rw [hval] at hpair'
    have hdist := axis_dist i₀ Yc hij
    have hdist' :
        t ^ 2 ≤ euclidNorm (((i * Yc : ℕ) : ℤ) • unit i₀ - ((j * Yc : ℕ) : ℤ) • unit i₀) :=
      le_trans hY1 hdist
    have hdist'' :
        t ^ 2 ≤ euclidNorm (((j * Yc : ℕ) : ℤ) • unit i₀ - ((i * Yc : ℕ) : ℤ) • unit i₀) := by
      rw [← neg_sub, CERW.Generic.Lattice.euclidNorm_neg]
      exact hdist'
    have hG : ∀ w : Site d, t ^ 2 ≤ euclidNorm w → srwGreenInf d w ≤ K / t ^ 2 := by
      intro w hw
      have h1 := hK w
      rw [latticeKernel_high hd, abs_neg, abs_of_nonneg (srwGreenInf_nonneg w)] at h1
      refine h1.trans ?_
      have hb : t ^ 2 ≤ 1 + euclidNorm w := by linarith
      have h2 : (1 + euclidNorm w) ^ (2 - (d : ℝ)) ≤ (t ^ 2) ^ (2 - (d : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hb (by
          have : (3 : ℝ) ≤ d := by exact_mod_cast hd
          linarith)
      have h3 : (t ^ 2) ^ (2 - (d : ℝ)) ≤ (t ^ 2) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by
          have : (3 : ℝ) ≤ d := by exact_mod_cast hd
          linarith)
      rw [Real.rpow_neg_one] at h3
      calc K * (1 + euclidNorm w) ^ (2 - (d : ℝ)) ≤ K * (t ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left (h2.trans h3) hK0
        _ = K / t ^ 2 := by rw [div_eq_mul_inv]
    have hT : srwGreenInf d (((i * Yc : ℕ) : ℤ) • unit i₀ - ((j * Yc : ℕ) : ℤ) • unit i₀) +
        srwGreenInf d (((j * Yc : ℕ) : ℤ) • unit i₀ - ((i * Yc : ℕ) : ℤ) • unit i₀) ≤
        2 * (K / t ^ 2) := by
      have := hG _ hdist'
      have := hG _ hdist''
      linarith
    have hT0 : 0 ≤ srwGreenInf d (((i * Yc : ℕ) : ℤ) • unit i₀ - ((j * Yc : ℕ) : ℤ) • unit i₀) +
        srwGreenInf d (((j * Yc : ℕ) : ℤ) • unit i₀ - ((i * Yc : ℕ) : ℤ) • unit i₀) :=
      add_nonneg (srwGreenInf_nonneg _) (srwGreenInf_nonneg _)
    have h2 := abs_le.mp hpair'
    rw [abs_le]
    have hkey : 2 * d * ε * (2 * (K / t ^ 2)) + C₁ / t ^ 2 ≤ (4 * d * ε * K + C₁ + 1) / t ^ 2 := by
      have : (4 * d * ε * K + C₁ + 1) / t ^ 2 = 4 * d * ε * (K / t ^ 2) + C₁ / t ^ 2 +
          1 / t ^ 2 := by ring
      rw [this]
      have : 0 ≤ 1 / t ^ 2 := by positivity
      nlinarith
    have hmul : 2 * (d : ℝ) * ε *
        (srwGreenInf d (((i * Yc : ℕ) : ℤ) • unit i₀ - ((j * Yc : ℕ) : ℤ) • unit i₀) +
          srwGreenInf d (((j * Yc : ℕ) : ℤ) • unit i₀ - ((i * Yc : ℕ) : ℤ) • unit i₀)) ≤
        2 * d * ε * (2 * (K / t ^ 2)) :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    have hmul0 : 0 ≤ 2 * (d : ℝ) * ε *
        (srwGreenInf d (((i * Yc : ℕ) : ℤ) • unit i₀ - ((j * Yc : ℕ) : ℤ) • unit i₀) +
          srwGreenInf d (((j * Yc : ℕ) : ℤ) • unit i₀ - ((i * Yc : ℕ) : ℤ) • unit i₀)) :=
      mul_nonneg (by positivity) hT0
    constructor <;> linarith [h2.1, h2.2]

/-- The total mass of `Γ` of a planar dipole of size `k` with itself. -/
private noncomputable def dipoleMass (k : ℕ) : ℝ :=
  2 * (latticeKernel 2 ((k : ℤ) • unit (0 : Fin 2)) +
    latticeKernel 2 (-((k : ℤ) • unit (0 : Fin 2)))) - 2

/-- The dipole mass is nonnegative. -/
private theorem dipoleMass_nonneg (k : ℕ) (hk : 1 ≤ k) : 0 ≤ dipoleMass k := by
  have h := planar_V k hk 0 ∅
  rw [Finset.sum_empty] at h
  exact h

/-- The dipole mass of size `k ≈ t` is comparable to `log t`. -/
private theorem planar_Vk : ∃ cV : ℝ, 0 ≤ cV ∧ ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ (t : ℝ) (k : ℕ), k₀ ≤ k →
    3 ≤ t → (k : ℝ) ≤ t → t / 2 ≤ k →
      dipoleMass k ≤ cV * Real.log t ∧ (cV ≤ Real.log t → Real.log t ≤ dipoleMass k) := by
  obtain ⟨Ca, hCa0, k₀, hk₀⟩ := planar_T_asymp
  refine ⟨3 + Ca, by positivity, max k₀ 1, le_max_right _ _, ?_⟩
  intro t k hk ht3 hkt hkt2
  have hk0 : k₀ ≤ k := le_trans (le_max_left _ _) hk
  have h1 := abs_le.mp (hk₀ k hk0)
  have hpi1 := Real.pi_gt_three
  have hpi2 := Real.pi_lt_d2
  have ht0 : 0 < t := by linarith
  have hkpos : (0 : ℝ) < k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast le_trans (le_max_right _ _) hk
    linarith
  have hlogt : 1 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le ht0]
    have := Real.exp_one_lt_d9
    linarith
  have hlk : Real.log k ≤ Real.log t := Real.log_le_log hkpos hkt
  have hlk2 : Real.log t - 1 ≤ Real.log k := by
    have h2 : Real.log (t / 2) ≤ Real.log k := Real.log_le_log (by positivity) hkt2
    rw [Real.log_div ht0.ne' (by norm_num)] at h2
    have := Real.log_two_lt_d9
    linarith
  have hc1 : 8 / Real.pi ≤ 3 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hc2 : (5 : ℝ) / 2 ≤ 8 / Real.pi := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hlk0 : 0 ≤ Real.log k := Real.log_nonneg (by
    have : (1 : ℝ) ≤ k := by exact_mod_cast le_trans (le_max_right _ _) hk
    exact this)
  unfold dipoleMass at *
  constructor
  · have : 8 / Real.pi * Real.log k ≤ 3 * Real.log t :=
      mul_le_mul hc1 hlk hlk0 (by norm_num)
    nlinarith
  · intro hc
    have : (5 : ℝ) / 2 * (Real.log t - 1) ≤ 8 / Real.pi * Real.log k :=
      mul_le_mul hc2 hlk2 (by linarith) (by positivity)
    nlinarith

/-- **The pair estimate for `d = 2`.** -/
private theorem planar_pair {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / ((2 : ℕ) : ℝ)) {P : ℝ}
    (hP : 0 ≤ P) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∃ k₁ : ℕ, 1 ≤ k₁ ∧ ∀ (t : ℝ) (k n : ℕ) (Y : ℕ → Site 2)
      (y y' : Site 2) (err : ℝ), k₁ ≤ k → 3 ≤ t → (k : ℝ) ≤ t → t / 2 ≤ k →
      euclidNorm y ≤ 2 * t ^ 3 → euclidNorm y' ≤ 2 * t ^ 3 → err ≤ P * t ^ 6 →
      (∀ x : Site 2,
        |(localTime Y n x : ℝ) - 2 * ((2 : ℕ) : ℝ) * ε * max (t ^ 8 - euclidNorm x) 0| ≤ err) →
      Real.log t ≥ 1 →
      |dynkinBracket (stepProb 2 ε) (dipole y k) (dipole y' k) Y n /
            (t ^ 8 * Real.log (t ^ 8)) -
        2 * ((2 : ℕ) : ℝ) * ε * t ^ 8 * (∑' x, gammaBr (dipole y k) (dipole y' k) x) /
          (t ^ 8 * Real.log (t ^ 8))| ≤ C₁ / t ^ 2 := by
  obtain ⟨cV, hcV0, k₀, hk₀1, hVk⟩ := planar_Vk
  obtain ⟨CW, hCW0, kW, hW⟩ := planar_W
  refine ⟨(12 * (cV + 2) + P * cV + 20 * ε * cV + 12 * ε * CW) / 8, by positivity,
    max k₀ kW, le_trans hk₀1 (le_max_left _ _), ?_⟩
  intro t k n Y y y' err hk ht3 hkt hkt2 hy hy' herr hprof hlog1
  have hk0 : k₀ ≤ k := le_trans (le_max_left _ _) hk
  have hkW : kW ≤ k := le_trans (le_max_right _ _) hk
  have hk1 : 1 ≤ k := le_trans hk₀1 hk0
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  set L : ℝ := Real.log t with hL
  have hlog8 : Real.log (t ^ 8) = 8 * L := by rw [Real.log_pow]; push_cast; ring
  have hV0 : 0 ≤ dipoleMass k := dipoleMass_nonneg k hk1
  have hVL : dipoleMass k ≤ cV * L := (hVk t k hk0 ht3 hkt hkt2).1
  have hWS : ∀ z : Site 2, euclidNorm z ≤ 2 * t ^ 3 → ∀ S : Finset (Site 2),
      ∑ x ∈ S, min (euclidNorm x) (t ^ 8) * gammaBr (dipole z k) (dipole z k) x ≤
        5 * t ^ 3 * dipoleMass k + 3 * CW * t ^ 5 := by
    intro z hz S
    refine (hW k hkW z (t ^ 8) (by positivity) S).trans ?_
    change (euclidNorm z + 3 * k) * dipoleMass k + CW * (k : ℝ) ^ 2 * (1 + euclidNorm z) ≤ _
    have hk' : (k : ℝ) ≤ t := hkt
    have hkn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 : (euclidNorm z + 3 * k) * dipoleMass k ≤ 5 * t ^ 3 * dipoleMass k := by
      apply mul_le_mul_of_nonneg_right _ hV0
      have : t ≤ t ^ 3 := by
        simpa using pow_le_pow_right₀ ht1 (show 1 ≤ 3 by norm_num)
      linarith
    have h2 : CW * (k : ℝ) ^ 2 * (1 + euclidNorm z) ≤ 3 * CW * t ^ 5 := by
      have h3 : (k : ℝ) ^ 2 * (1 + euclidNorm z) ≤ 3 * t ^ 5 := by
        have hk2 : (k : ℝ) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hkn hk' 2
        have ht25 : t ^ 2 ≤ t ^ 5 := pow_le_pow_right₀ ht1 (by norm_num)
        have : (k : ℝ) ^ 2 * (1 + euclidNorm z) ≤ t ^ 2 * (1 + 2 * t ^ 3) :=
          mul_le_mul hk2 (by linarith) (by linarith [euclidNorm_nonneg z]) (by positivity)
        nlinarith
      calc CW * (k : ℝ) ^ 2 * (1 + euclidNorm z) = CW * ((k : ℝ) ^ 2 * (1 + euclidNorm z)) := by
            ring
        _ ≤ CW * (3 * t ^ 5) := mul_le_mul_of_nonneg_left h3 hCW0
        _ = 3 * CW * t ^ 5 := by ring
    linarith
  have hmain := bracket_approx (d := 2) (by norm_num) hε0.le hε1 Y n (t ^ 8) err
    (dipoleMass k) (5 * t ^ 3 * dipoleMass k + 3 * CW * t ^ 5) 2 (by positivity) hprof
    (dipole y k) (dipole y' k) (planar_V k hk1 y) (planar_V k hk1 y') (hWS y hy) (hWS y' hy')
    (planar_D k hk1 y) (planar_D k hk1 y')
  have ht6 : t ^ 3 ≤ t ^ 6 := pow_le_pow_right₀ ht1 (by norm_num)
  have ht56 : t ^ 5 ≤ t ^ 6 := pow_le_pow_right₀ ht1 (by norm_num)
  have ht60 : (1 : ℝ) ≤ t ^ 6 := one_le_pow₀ ht1
  have hE : 6 * ((2 : ℕ) : ℝ) * (dipoleMass k + 2) + err * dipoleMass k +
      2 * ((2 : ℕ) : ℝ) * ε * (5 * t ^ 3 * dipoleMass k + 3 * CW * t ^ 5) ≤
      (12 * (cV + 2) + P * cV + 20 * ε * cV + 12 * ε * CW) * t ^ 6 * L := by
    push_cast
    have a1 : 12 * (dipoleMass k + 2) ≤ 12 * (cV + 2) * t ^ 6 * L := by
      have : dipoleMass k + 2 ≤ (cV + 2) * L := by nlinarith
      have h := mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 12)
      have h12 : (0 : ℝ) ≤ 12 * (cV + 2) := by linarith
      have : 12 * ((cV + 2) * L) ≤ 12 * (cV + 2) * t ^ 6 * L := by
        nlinarith [mul_nonneg h12 (by linarith : (0 : ℝ) ≤ L)]
      linarith
    have a2 : err * dipoleMass k ≤ P * cV * t ^ 6 * L := by
      have h1 := mul_le_mul herr hVL hV0 (by positivity)
      nlinarith
    have a3 : 4 * ε * (5 * t ^ 3 * dipoleMass k) ≤ 20 * ε * cV * t ^ 6 * L := by
      have h1 : t ^ 3 * dipoleMass k ≤ t ^ 6 * (cV * L) :=
        mul_le_mul ht6 hVL hV0 (by positivity)
      nlinarith
    have a4 : 4 * ε * (3 * CW * t ^ 5) ≤ 12 * ε * CW * t ^ 6 * L := by
      have : t ^ 5 ≤ t ^ 6 * L := by nlinarith
      have h5 : 0 ≤ 12 * ε * CW := by positivity
      nlinarith
    nlinarith
  have hkey := hmain.trans hE
  have hSpos : 0 < t ^ 8 * Real.log (t ^ 8) := by rw [hlog8]; positivity
  have heq : dynkinBracket (stepProb 2 ε) (dipole y k) (dipole y' k) Y n /
            (t ^ 8 * Real.log (t ^ 8)) -
        2 * ((2 : ℕ) : ℝ) * ε * t ^ 8 * (∑' x, gammaBr (dipole y k) (dipole y' k) x) /
          (t ^ 8 * Real.log (t ^ 8)) =
      (dynkinBracket (stepProb 2 ε) (dipole y k) (dipole y' k) Y n -
        2 * ((2 : ℕ) : ℝ) * ε * t ^ 8 * ∑' x, gammaBr (dipole y k) (dipole y' k) x) /
          (t ^ 8 * Real.log (t ^ 8)) := by ring
  rw [heq, abs_div, abs_of_pos hSpos]
  calc _ ≤ (12 * (cV + 2) + P * cV + 20 * ε * cV + 12 * ε * CW) * t ^ 6 * L /
        (t ^ 8 * Real.log (t ^ 8)) := div_le_div_of_nonneg_right hkey hSpos.le
    _ = (12 * (cV + 2) + P * cV + 20 * ε * cV + 12 * ε * CW) / 8 / t ^ 2 := by
        rw [hlog8]
        have : L ≠ 0 := by positivity
        field_simp

/-- The off-diagonal bound from the main term `ε T / (2 L)` and the error `C₁ / t²`. -/
private theorem off_diag_final {ε CT C₁ t T B L : ℝ} (hε0 : 0 < ε) (hL1 : 1 ≤ L) (ht0 : 0 < t)
    (hT : |T| ≤ CT / t ^ 2) (hB : |B - ε * T / (2 * L)| ≤ C₁ / t ^ 2) :
    |B| ≤ (ε * CT + C₁ + 1) / t ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hm : |ε * T / (2 * L)| ≤ ε * CT / t ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos hε0, abs_of_pos (by positivity : 0 < 2 * L)]
    calc ε * |T| / (2 * L) ≤ ε * |T| :=
          div_le_self (mul_nonneg hε0.le (abs_nonneg T)) (by linarith)
      _ ≤ ε * (CT / t ^ 2) := mul_le_mul_of_nonneg_left hT hε0.le
      _ = ε * CT / t ^ 2 := by ring
  have h3 : |B| ≤ |B - ε * T / (2 * L)| + |ε * T / (2 * L)| := by
    have := abs_add_le (B - ε * T / (2 * L)) (ε * T / (2 * L))
    rwa [sub_add_cancel] at this
  have h4 : (ε * CT + C₁ + 1) / t ^ 2 = ε * CT / t ^ 2 + C₁ / t ^ 2 + 1 / t ^ 2 := by ring
  have h5 : 0 ≤ 1 / t ^ 2 := by positivity
  rw [h4]
  linarith

/-- **The brackets for `d = 2`**: for large `t`, the normalized diagonal brackets lie between
two positive constants and the off-diagonal ones are at most `C / t²`. -/
private theorem assembly_planar {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / ((2 : ℕ) : ℝ)) {P : ℝ}
    (hP : 0 ≤ P) :
    ∃ t₀ c₀ C₀ C : ℝ, 3 ≤ t₀ ∧ 0 < c₀ ∧ c₀ ≤ C₀ ∧ 0 < C ∧
      ∀ (t : ℝ) (Yc k m n : ℕ) (Y : ℕ → Site 2) (err : ℝ), t₀ ≤ t → t ^ 2 ≤ Yc →
        (Yc : ℝ) ≤ 2 * t ^ 2 → (m : ℝ) ≤ t → (k : ℝ) ≤ t → t / 2 ≤ k → err ≤ P * t ^ 6 →
        (∀ x : Site 2,
          |(localTime Y n x : ℝ) - 2 * ((2 : ℕ) : ℝ) * ε * max (t ^ 8 - euclidNorm x) 0| ≤
            err) →
        ∀ i j : ℕ, 1 ≤ i → i ≤ m → 1 ≤ j → j ≤ m → ∀ B : ℝ,
          B = dynkinBracket (stepProb 2 ε)
            (dipole (((i * Yc : ℕ) : ℤ) • unit (0 : Fin 2)) k)
            (dipole (((j * Yc : ℕ) : ℤ) • unit (0 : Fin 2)) k) Y n /
              (t ^ 8 * Real.log (t ^ 8)) →
          (i = j → c₀ ≤ B ∧ B ≤ C₀) ∧ (i ≠ j → |B| ≤ C / t ^ 2) := by
  obtain ⟨C₁, hC₁0, k₁, hk₁1, hpair⟩ := planar_pair hε0 hε1 hP
  obtain ⟨cV, hcV0, k₀, hk₀1, hVk⟩ := planar_Vk
  obtain ⟨CT, hCT0, kT, hT⟩ := planar_T_off
  have hε1' : ε < 1 / 2 := by simpa using hε1
  set K₀ : ℕ := max k₁ (max k₀ kT) with hK₀
  refine ⟨max (max 3 (2 * (K₀ : ℝ))) (max (Real.exp cV) (4 * C₁ / ε + 1)), ε / 4,
    ε * cV / 2 + 1, ε * CT + C₁ + 1, le_trans (le_max_left _ _) (le_max_left _ _),
    by positivity, ?_, by positivity, ?_⟩
  · nlinarith [mul_nonneg hε0.le hcV0]
  intro t Yc k m n Y err ht hY1 hY2 hm hkt hkt2 herr hprof i j hi1 him hj1 hjm B hB
  have ht3 : 3 ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have ht2K : 2 * (K₀ : ℝ) ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have hteC : Real.exp cV ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htC : 4 * C₁ / ε + 1 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hkK : K₀ ≤ k := by
    have : (K₀ : ℝ) ≤ k := by linarith
    exact_mod_cast this
  have hk₁k : k₁ ≤ k := le_trans (le_max_left _ _) hkK
  have hk₀k : k₀ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hkK
  have hkTk : kT ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hkK
  have hk1 : 1 ≤ k := le_trans hk₁1 hk₁k
  have hL1 : 1 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le ht0]
    have := Real.exp_one_lt_d9
    linarith
  have hcVL : cV ≤ Real.log t := by
    have := Real.log_le_log (Real.exp_pos cV) hteC
    rwa [Real.log_exp] at this
  have hlog8 : Real.log (t ^ 8) = 8 * Real.log t := by rw [Real.log_pow]; push_cast; ring
  have hYc1 : 1 ≤ Yc := by
    have : (1 : ℝ) ≤ Yc := le_trans (by nlinarith) hY1
    exact_mod_cast this
  have hsmall : C₁ / t ^ 2 ≤ ε / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 4 * C₁ / ε ≤ t := by linarith
    rw [div_le_iff₀ hε0] at h1
    nlinarith
  have hnorm : ∀ i : ℕ, 1 ≤ i → i ≤ m →
      euclidNorm (((i * Yc : ℕ) : ℤ) • unit (0 : Fin 2)) ≤ 2 * t ^ 3 := by
    intro i hi1 him
    rw [axis_norm]
    have h1 : (i : ℝ) ≤ t := le_trans (by exact_mod_cast him) hm
    calc (i : ℝ) * Yc ≤ t * (2 * t ^ 2) :=
          mul_le_mul h1 hY2 (Nat.cast_nonneg Yc) ht0.le
      _ = 2 * t ^ 3 := by ring
  have hpair' := hpair t k n Y _ _ err hk₁k ht3 hkt hkt2 (hnorm i hi1 him) (hnorm j hj1 hjm)
    herr hprof hL1
  rw [← hB] at hpair'
  have hmain : ∀ T : ℝ, 2 * ((2 : ℕ) : ℝ) * ε * t ^ 8 * T / (t ^ 8 * Real.log (t ^ 8)) =
      ε * T / (2 * Real.log t) := by
    intro T
    rw [hlog8]
    have : Real.log t ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  constructor
  · rintro rfl
    obtain ⟨hs, hv⟩ := planar_T_diag k hk1 (((i * Yc : ℕ) : ℤ) • unit (0 : Fin 2))
    rw [hv, hmain] at hpair'
    have hV := hVk t k hk₀k ht3 hkt hkt2
    have hV1 : Real.log t ≤ dipoleMass k := hV.2 hcVL
    have hV2 : dipoleMass k ≤ cV * Real.log t := hV.1
    have hL0 : 0 < Real.log t := by linarith
    have hq1 : ε / 2 ≤ ε * (2 * (latticeKernel 2 ((k : ℤ) • unit (0 : Fin 2)) +
        latticeKernel 2 (-((k : ℤ) • unit (0 : Fin 2)))) - 2) / (2 * Real.log t) := by
      rw [le_div_iff₀ (by positivity)]
      have : Real.log t ≤ 2 * (latticeKernel 2 ((k : ℤ) • unit (0 : Fin 2)) +
          latticeKernel 2 (-((k : ℤ) • unit (0 : Fin 2)))) - 2 := hV1
      nlinarith
    have hq2 : ε * (2 * (latticeKernel 2 ((k : ℤ) • unit (0 : Fin 2)) +
        latticeKernel 2 (-((k : ℤ) • unit (0 : Fin 2)))) - 2) / (2 * Real.log t) ≤
        ε * cV / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : 2 * (latticeKernel 2 ((k : ℤ) • unit (0 : Fin 2)) +
          latticeKernel 2 (-((k : ℤ) • unit (0 : Fin 2)))) - 2 ≤ cV * Real.log t := hV2
      nlinarith
    have h2 := abs_le.mp hpair'
    constructor
    · linarith [h2.1, h2.2]
    · linarith [h2.1, h2.2]
  · intro hij
    have hsep := axis_sep_abs Yc hij
    have h2k : 2 * (k : ℤ) ≤ |((i * Yc : ℕ) : ℤ) - ((j * Yc : ℕ) : ℤ)| := by
      have h1 : 2 * (k : ℝ) ≤ Yc := by nlinarith
      have h2 : 2 * (k : ℝ) ≤ |((((i * Yc : ℕ) : ℤ) - ((j * Yc : ℕ) : ℤ) : ℤ) : ℝ)| :=
        le_trans h1 hsep
      exact_mod_cast h2
    obtain ⟨hs, hbound⟩ := hT k hkTk ((i * Yc : ℕ) : ℤ) ((j * Yc : ℕ) : ℤ) h2k
    rw [hmain] at hpair'
    set T : ℝ := ∑' x, gammaBr (dipole (((i * Yc : ℕ) : ℤ) • unit (0 : Fin 2)) k)
      (dipole (((j * Yc : ℕ) : ℤ) • unit (0 : Fin 2)) k) x with hTdef
    have hD : t ^ 4 ≤ ((((i * Yc : ℕ) : ℤ) - ((j * Yc : ℕ) : ℤ) : ℤ) : ℝ) ^ 2 := by
      rw [← sq_abs]
      have h1 : t ^ 2 ≤ |((((i * Yc : ℕ) : ℤ) - ((j * Yc : ℕ) : ℤ) : ℤ) : ℝ)| :=
        le_trans hY1 hsep
      calc t ^ 4 = (t ^ 2) ^ 2 := by ring
        _ ≤ _ := pow_le_pow_left₀ (by positivity) h1 2
    have hk2 : (k : ℝ) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg k) hkt 2
    have hT' : |T| ≤ CT / t ^ 2 := by
      refine hbound.trans ?_
      calc CT * (k : ℝ) ^ 2 / ((((i * Yc : ℕ) : ℤ) - ((j * Yc : ℕ) : ℤ) : ℤ) : ℝ) ^ 2
          ≤ CT * t ^ 2 / t ^ 4 := by
            apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hk2 hCT0)
              (by positivity) hD
        _ = CT / t ^ 2 := by field_simp
    exact off_diag_final hε0 hL1 ht0 hT' hpair'

/-! ### The scales -/

/-- The scale `r_n = ((d+1) n / (2 d ε ω_d))^{1/(d+1)}`. -/
private noncomputable def radius (d : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  (((d : ℝ) + 1) * n / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1))

/-- The constant `A = (d+1)/(2 d ε ω_d)` with `r_n = (A n)^{1/(d+1)}`. -/
private noncomputable def scaleConst (d : ℕ) (ε : ℝ) : ℝ :=
  ((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d)

/-- The constant `A` is positive. -/
private theorem scaleConst_pos (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) : 0 < scaleConst d ε := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  unfold scaleConst
  exact div_pos (by positivity) (mul_pos (mul_pos (mul_pos (by norm_num) hd0) hε)
    (unitBallVolume_pos d))

/-- `r_n = (A n)^{1/(d+1)}`. -/
private theorem radius_eq (d : ℕ) (ε : ℝ) (n : ℕ) :
    radius d ε n = (scaleConst d ε * n) ^ ((1 : ℝ) / (d + 1)) := by
  unfold radius scaleConst
  congr 1
  ring

/-- `r_n → ∞`. -/
private theorem radius_tendsto (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (radius d ε) atTop atTop := by
  have hq : 0 < (1 : ℝ) / (d + 1) := by positivity
  have hA := scaleConst_pos hd hε
  have h1 : Tendsto (fun n : ℕ => scaleConst d ε * n) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hA
  have h2 := (tendsto_rpow_atTop hq).comp h1
  refine h2.congr fun n => ?_
  rw [radius_eq]
  rfl

/-- Powers of `log (n + 2)` are negligible against positive powers of `r_n`. -/
private theorem log_rpow_div_radius_rpow (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (a : ℝ)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.log (n + 2) ^ a / radius d ε n ^ c) atTop (𝓝 0) := by
  have hq : 0 < (1 : ℝ) / (d + 1) := by positivity
  have hA := scaleConst_pos hd hε
  have h := (CERW.Support.Main.tendsto_log_rpow_div_rpow a
    (c := (1 / ((d : ℝ) + 1)) * c) (mul_pos hq hc)).div_const
    (scaleConst d ε ^ ((1 / ((d : ℝ) + 1)) * c))
  rw [zero_div] at h
  refine h.congr fun n => ?_
  rw [radius_eq, ← Real.rpow_mul (mul_nonneg hA.le (Nat.cast_nonneg n)),
    Real.mul_rpow hA.le (Nat.cast_nonneg n), div_div, mul_comm]

/-- For large `n`, `t_n = r_n^{1/8}` is at least `t₀`, `r_n ≥ 1`, and `(log n)^{3/2} ≤ t_n²`. -/
private theorem scale_eventually (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (t₀ : ℝ) :
    ∀ᶠ n : ℕ in atTop, t₀ ≤ radius d ε n ^ ((1 : ℝ) / 8) ∧
      Real.log n ^ ((3 : ℝ) / 2) ≤ (radius d ε n ^ ((1 : ℝ) / 8)) ^ 2 := by
  have hrt := radius_tendsto hd hε
  have h1 : ∀ᶠ n : ℕ in atTop, t₀ ≤ radius d ε n ^ ((1 : ℝ) / 8) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp hrt).eventually_ge_atTop t₀
  have h2 := (log_rpow_div_radius_rpow hd hε ((3 : ℝ) / 2) (c := 1 / 4) (by norm_num)
    ).eventually_lt_const one_pos
  filter_upwards [h1, h2, hrt.eventually_gt_atTop 0, eventually_ge_atTop 1] with n hn1 hn2 hn3 hn4
  refine ⟨hn1, ?_⟩
  have hsq : (radius d ε n ^ ((1 : ℝ) / 8)) ^ 2 = radius d ε n ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn3.le]
    norm_num
  rw [hsq]
  have hpos : 0 < radius d ε n ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hn3 _
  have h3 : Real.log (n + 2) ^ ((3 : ℝ) / 2) < radius d ε n ^ ((1 : ℝ) / 4) := by
    rwa [div_lt_one hpos] at hn2
  refine le_trans ?_ h3.le
  apply Real.rpow_le_rpow (Real.log_nonneg (by exact_mod_cast hn4))
  · exact Real.log_le_log (by exact_mod_cast hn4) (by linarith)
  · norm_num

/-- `r_n` is nonnegative. -/
private theorem radius_nonneg (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    0 ≤ radius d ε n := by
  rw [radius_eq]
  exact Real.rpow_nonneg (mul_nonneg (scaleConst_pos hd hε).le (Nat.cast_nonneg n)) _

/-- For `L ≥ 1`, `√(ρ L) ≤ √ρ L^{3/2}`. -/
private theorem sqrt_mul_le_sqrt_mul_rpow {ρ L : ℝ} (hρ : 0 ≤ ρ) (hL : 1 ≤ L) :
    Real.sqrt (ρ * L) ≤ Real.sqrt ρ * L ^ ((3 : ℝ) / 2) := by
  rw [Real.sqrt_mul hρ]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg ρ)
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)


/-- The eighth power of the eighth root. -/
private theorem rpow_eighth_pow {ρ : ℝ} (hρ : 0 < ρ) : (ρ ^ ((1 : ℝ) / 8)) ^ 8 = ρ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
  norm_num

/-- The square of the eighth root is the fourth root. -/
private theorem rpow_eighth_sq {ρ : ℝ} (hρ : 0 < ρ) :
    (ρ ^ ((1 : ℝ) / 8)) ^ 2 = ρ ^ ((1 : ℝ) / 4) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
  norm_num

/-- The square root is the fourth power of the eighth root. -/
private theorem sqrt_eq_rpow_eighth {ρ : ℝ} (hρ : 0 < ρ) :
    Real.sqrt ρ = (ρ ^ ((1 : ℝ) / 8)) ^ 4 := by
  have h : ρ = ((ρ ^ ((1 : ℝ) / 8)) ^ 4) ^ 2 := by
    rw [← pow_mul]
    exact (rpow_eighth_pow hρ).symm
  conv_lhs => rw [h]
  exact Real.sqrt_sq (by positivity)

/-- The power `-1/4` is the inverse of the square of the eighth root. -/
private theorem rpow_neg_quarter {ρ : ℝ} (hρ : 0 < ρ) :
    ρ ^ (-(1 : ℝ) / 4) = 1 / (ρ ^ ((1 : ℝ) / 8)) ^ 2 := by
  rw [rpow_eighth_sq hρ, one_div, ← Real.rpow_neg hρ.le]
  norm_num

/-- If `r_n^{1/8}` is at least a positive number, then `r_n` is positive. -/
private theorem radius_pos_of (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {n : ℕ} {t₀ : ℝ}
    (ht₀ : 0 < t₀) (h : t₀ ≤ radius d ε n ^ ((1 : ℝ) / 8)) : 0 < radius d ε n := by
  have hA := scaleConst_pos hd hε
  have h0 : 0 ≤ radius d ε n := by
    rw [radius_eq]
    exact Real.rpow_nonneg (mul_nonneg hA.le (Nat.cast_nonneg n)) _
  refine lt_of_le_of_ne h0 fun h1 => ?_
  rw [← h1, Real.zero_rpow (by norm_num)] at h
  linarith

/-- **The deterministic core**: on the profile event, the brackets of the statement satisfy
the required bounds for all large `n`. -/
private theorem brackets_core {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1 / (d : ℝ)) {P : ℝ} (hP : 0 ≤ P) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let e₁ : Site d := LatticeProb.unit ⟨0, by omega⟩
    let g : Site d → ℝ := CERW.latticeKernel d
    let σ : ℕ → ℝ := fun n =>
      if d = 2 then Real.sqrt (r n * Real.log (r n)) else Real.sqrt (r n)
    let k : ℕ → ℕ := fun n => ⌊r n ^ ((1 : ℝ) / 8)⌋₊
    let m : ℕ → ℕ := fun n => ⌊r n ^ ((1 : ℝ) / 8)⌋₊
    let y : ℕ → ℕ → Site d := fun n i => ((i * ⌈r n ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℤ) • e₁
    let f : ℕ → ℕ → Site d → ℝ := fun n i z =>
      if d = 2 then g (z - (y n i + (k n : ℤ) • e₁)) - g (z - y n i) else g (z - y n i)
    ∃ c₀ C₀ C : ℝ, 0 < c₀ ∧ c₀ ≤ C₀ ∧ 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ Y : ℕ → Site d,
      (∀ x : Site d, |(localTime Y n x : ℝ) - 2 * d * ε * max (r n - euclidNorm x) 0| ≤
        P * (Real.sqrt (r n) * Real.log n ^ ((3 : ℝ) / 2))) →
      ∀ i j : ℕ, 1 ≤ i → i ≤ m n → 1 ≤ j → j ≤ m n →
        let B : ℝ := CERW.dynkinBracket (CERW.stepProb d ε) (f n i) (f n j) Y n / σ n ^ 2
        (i = j → c₀ ≤ B ∧ B ≤ C₀) ∧ (i ≠ j → |B| ≤ C * r n ^ (-(1 : ℝ) / 4)) := by
  intro ωd r e₁ g σ k m y f
  have hrr : ∀ n, r n = radius d ε n := fun n => rfl
  by_cases h2 : d = 2
  · subst h2
    obtain ⟨t₀, c₀, C₀, C, ht₀, hc₀, hcC, hC, hmain⟩ := assembly_planar hε0 hε1 hP
    obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp (scale_eventually hd hε0 t₀)
    refine ⟨c₀, C₀, C, hc₀, hcC, hC, n₁, ?_⟩
    intro n hn Y hprof i j hi1 him hj1 hjm B
    obtain ⟨ht, hlog⟩ := hn₁ n hn
    rw [← hrr n] at ht hlog
    have hr0 : 0 < r n := by
      rw [hrr]
      exact radius_pos_of (t₀ := t₀) hd hε0 (by linarith) (by rw [← hrr n]; exact ht)
    set t : ℝ := r n ^ ((1 : ℝ) / 8) with htdef
    have hrt8 : r n = t ^ 8 := (rpow_eighth_pow hr0).symm
    have ht3 : 3 ≤ t := le_trans ht₀ ht
    have ht1 : 1 ≤ t := by linarith
    have hr1 : 1 ≤ r n := by rw [hrt8]; exact one_le_pow₀ ht1
    have hsq : Real.sqrt (r n) = t ^ 4 := sqrt_eq_rpow_eighth hr0
    have hσ : σ n ^ 2 = t ^ 8 * Real.log (t ^ 8) := by
      simp only [σ, if_true]
      rw [Real.sq_sqrt (mul_nonneg hr0.le (Real.log_nonneg hr1)), hrt8]
    have hY : t ^ 2 = r n ^ ((1 : ℝ) / 4) := rpow_eighth_sq hr0
    have hY1 : t ^ 2 ≤ ((⌈r n ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℝ) := by
      rw [hY]
      exact Nat.le_ceil _
    have hY2 : ((⌈r n ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℝ) ≤ 2 * t ^ 2 := by
      have h3 : ((⌈r n ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℝ) < t ^ 2 + 1 := by
        rw [hY]
        exact Nat.ceil_lt_add_one (Real.rpow_nonneg hr0.le ((1 : ℝ) / 4))
      have h4 : 1 ≤ t ^ 2 := one_le_pow₀ ht1
      linarith
    have hm : ((m n : ℕ) : ℝ) ≤ t := Nat.floor_le (by positivity)
    have hkt : ((k n : ℕ) : ℝ) ≤ t := Nat.floor_le (by positivity)
    have hkt2 : t / 2 ≤ ((k n : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one t
      change t < ((k n : ℕ) : ℝ) + 1 at this
      linarith
    have herr : P * (Real.sqrt (r n) * Real.log n ^ ((3 : ℝ) / 2)) ≤ P * t ^ 6 := by
      rw [hsq]
      have h1 : t ^ 4 * Real.log n ^ ((3 : ℝ) / 2) ≤ t ^ 4 * t ^ 2 :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      have h2 : t ^ 4 * t ^ 2 = t ^ 6 := by ring
      exact mul_le_mul_of_nonneg_left (h1.trans h2.le) hP
    have hprof' : ∀ x : Site 2, |(localTime Y n x : ℝ) - 2 * ((2 : ℕ) : ℝ) * ε *
        max (t ^ 8 - euclidNorm x) 0| ≤ P * (Real.sqrt (r n) * Real.log n ^ ((3 : ℝ) / 2)) := by
      intro x
      have h := hprof x
      rwa [show max (r n - euclidNorm x) 0 = max (t ^ 8 - euclidNorm x) 0 by rw [← hrt8]] at h
    have hf : ∀ i : ℕ, f n i = dipole (((i * ⌈r n ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℤ) • unit (0 : Fin 2))
        (k n) := by
      intro i
      funext z
      rfl
    have hB : B = dynkinBracket (stepProb 2 ε)
        (dipole (((i * ⌈r n ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℤ) • unit (0 : Fin 2)) (k n))
        (dipole (((j * ⌈r n ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℤ) • unit (0 : Fin 2)) (k n)) Y n /
          (t ^ 8 * Real.log (t ^ 8)) := by
      rw [← hσ, ← hf i, ← hf j]
    obtain ⟨hdiag, hoff⟩ := hmain t ⌈r n ^ ((1 : ℝ) / 4)⌉₊ (k n) (m n) n Y _ ht hY1 hY2 hm hkt
      hkt2 herr hprof' i j hi1 him hj1 hjm B hB
    refine ⟨hdiag, fun hij => ?_⟩
    rw [rpow_neg_quarter hr0]
    calc |B| ≤ C / t ^ 2 := hoff hij
      _ = C * (1 / t ^ 2) := by ring
  · have hd3 : 3 ≤ d := by omega
    obtain ⟨t₀, c₀, C₀, C, ht₀, hc₀, hcC, hC, hmain⟩ :=
      assembly_high hd3 (⟨0, by omega⟩ : Fin d) hε0 hε1 hP
    obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp (scale_eventually hd hε0 t₀)
    refine ⟨c₀, C₀, C, hc₀, hcC, hC, n₁, ?_⟩
    intro n hn Y hprof i j hi1 him hj1 hjm B
    obtain ⟨ht, hlog⟩ := hn₁ n hn
    rw [← hrr n] at ht hlog
    have hr0 : 0 < r n := by
      rw [hrr]
      exact radius_pos_of (t₀ := t₀) hd hε0 (by linarith) (by rw [← hrr n]; exact ht)
    set t : ℝ := r n ^ ((1 : ℝ) / 8) with htdef
    have hrt8 : r n = t ^ 8 := (rpow_eighth_pow hr0).symm
    have ht1 : 1 ≤ t := le_trans ht₀ ht
    have hsq : Real.sqrt (r n) = t ^ 4 := sqrt_eq_rpow_eighth hr0
    have hσ : σ n ^ 2 = t ^ 8 := by
      simp only [σ, if_neg h2]
      rw [Real.sq_sqrt hr0.le, hrt8]
    have hY : t ^ 2 = r n ^ ((1 : ℝ) / 4) := rpow_eighth_sq hr0
    have hY1 : t ^ 2 ≤ ((⌈r n ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℝ) := by
      rw [hY]
      exact Nat.le_ceil _
    have hY2 : ((⌈r n ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℝ) ≤ 2 * t ^ 2 := by
      have h3 : ((⌈r n ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℝ) < t ^ 2 + 1 := by
        rw [hY]
        exact Nat.ceil_lt_add_one (Real.rpow_nonneg hr0.le ((1 : ℝ) / 4))
      have h4 : 1 ≤ t ^ 2 := one_le_pow₀ ht1
      linarith
    have hm : ((m n : ℕ) : ℝ) ≤ t := Nat.floor_le (by positivity)
    have herr : P * (Real.sqrt (r n) * Real.log n ^ ((3 : ℝ) / 2)) ≤ P * t ^ 6 := by
      rw [hsq]
      have h1 : t ^ 4 * Real.log n ^ ((3 : ℝ) / 2) ≤ t ^ 4 * t ^ 2 :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      have h2 : t ^ 4 * t ^ 2 = t ^ 6 := by ring
      exact mul_le_mul_of_nonneg_left (h1.trans h2.le) hP
    have hprof' : ∀ x : Site d, |(localTime Y n x : ℝ) - 2 * d * ε *
        max (t ^ 8 - euclidNorm x) 0| ≤ P * (Real.sqrt (r n) * Real.log n ^ ((3 : ℝ) / 2)) := by
      intro x
      have h := hprof x
      rwa [show max (r n - euclidNorm x) 0 = max (t ^ 8 - euclidNorm x) 0 by rw [← hrt8]] at h
    have hf : ∀ i : ℕ, f n i = fun z => latticeKernel d
        (z - ((i * ⌈r n ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℤ) • unit (⟨0, by omega⟩ : Fin d)) := by
      intro i
      funext z
      simp only [f, y, e₁, g, if_neg h2]
    have hB : B = dynkinBracket (stepProb d ε)
        (fun z => latticeKernel d
          (z - ((i * ⌈r n ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℤ) • unit (⟨0, by omega⟩ : Fin d)))
        (fun z => latticeKernel d
          (z - ((j * ⌈r n ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℤ) • unit (⟨0, by omega⟩ : Fin d))) Y n /
          t ^ 8 := by
      rw [← hσ, ← hf i, ← hf j]
    obtain ⟨hdiag, hoff⟩ := hmain t ⌈r n ^ ((1 : ℝ) / 4)⌉₊ (m n) n Y _ ht hY1 hY2 hm
      herr hprof' i j hi1 him hj1 hjm B hB
    refine ⟨hdiag, fun hij => ?_⟩
    rw [rpow_neg_quarter hr0]
    calc |B| ≤ C / t ^ 2 := hoff hij
      _ = C * (1 / t ^ 2) := by ring

end Helpers

/-- **Lemma 9.3 (separated brackets)**: from the fluctuation rates, with probability at least
`1 - C n^{-10}` the normalized pathwise brackets of the martingales `S^i` have diagonal entries
between two positive constants and off-diagonal entries of size `O(r_n^{-1/4})`. -/
theorem separated_brackets_of (hfluct : fluctuation_rates.{u}) :
    separated_brackets.{u} := by
  intro d hd ωd ε hε0 hε1 r e₁ g σ k m y f
  obtain ⟨Cf, hCf, hprob, -⟩ := hfluct hd ε hε0 hε1 10 (by norm_num)
  obtain ⟨c₀, C₀, C, hc₀, hcC, hC, n₀, hcore⟩ := brackets_core hd hε0 hε1 hCf.le
  have hr0 : ∀ n, 0 ≤ r n := fun n => radius_nonneg hd hε0 n
  refine ⟨c₀, C₀, max C Cf, hc₀, hcC, lt_max_of_lt_left hC, max n₀ 3, ?_⟩
  intro Ω _ μ _ X hX n hn
  refine le_trans (measure_mono ?_) ((hprob μ X hX n (by omega)).trans ?_)
  · intro ω hω hgood
    apply hω
    obtain ⟨-, -, hloc⟩ := hgood
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
    have hlog : 1 ≤ Real.log n := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    have hloc' : ∀ x : Site d,
        |(localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - euclidNorm x) 0| ≤
          Cf * (Real.sqrt (r n) * Real.log n ^ ((3 : ℝ) / 2)) := by
      intro x
      refine (hloc x).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCf.le
      split_ifs
      · exact le_rfl
      · exact sqrt_mul_le_sqrt_mul_rpow (hr0 n) hlog
    intro i j hi1 him hj1 hjm
    have h := hcore n (le_trans (le_max_left _ _) hn) (fun j => X j ω) hloc' i j hi1 him hj1 hjm
    refine ⟨h.1, fun hij => (h.2 hij).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (hr0 n) _)
  · apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

end CERW.Support.Lower
