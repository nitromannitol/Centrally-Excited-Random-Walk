import LatticeProb.Walk.SimpleTransfer
import LatticeProb.Walk.ExteriorDirichlet
import LatticeProb.Walk.SRWSup

/-!
# The Poisson equation for the lattice potential kernel

`(P - I) b = 1_{0}` in both cases of the paper (`local-times.tex`, the definition of `b`). If
`b(x)` is the limit of the partial sums `Σ_{j<M} [P^j(0,0) - P^j(0,x)]`, then applying `P` to
the partial sums telescopes. `P (Σ_{j<M} P^j(0,·))(x) = Σ_{j<M} P^{j+1}(0,x)`, so
`(P - I)` of the `M`-th partial sum is `1_{0}(x) - P^M(0,x)`, and `P^M(0,x) → 0`. For `d ≥ 3`,
`b = -G` and the identity is the library's `walkOp_srwGreenInf`.
-/

namespace CERW.Support.LocalTime

open Filter Topology LatticeProb

variable {d : ℕ}

/-- In dimension `d ≥ 1`, `P^M(0, x) → 0` as `M → ∞`. -/
theorem tendsto_srwHeat_zero (hd : 1 ≤ d) (x : Site d) :
    Tendsto (fun M : ℕ => srwHeat d M x) atTop (𝓝 0) := by
  have hd0 : 0 < d := hd
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hypos : (0 : ℝ) < (d : ℝ) / 2 := div_pos hdR (by norm_num)
  have hpow : Tendsto (fun t : ℝ => t ^ (-(d : ℝ) / 2)) atTop (𝓝 0) := by
    simpa only [neg_div] using tendsto_rpow_neg_atTop (y := (d : ℝ) / 2) hypos
  have hcomp : Tendsto (fun M : ℕ => (M : ℝ) ^ (-(d : ℝ) / 2)) atTop (𝓝 0) :=
    hpow.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto
      (fun M : ℕ => Real.sqrt 2 ^ d * greenConst d * (M : ℝ) ^ (-(d : ℝ) / 2))
      atTop (𝓝 0) := by
    have hmul := hcomp.const_mul (Real.sqrt 2 ^ d * greenConst d)
    simpa using hmul
  refine squeeze_zero' (Eventually.of_forall fun M => srwHeat_nonneg M x) ?_ hc
  filter_upwards [eventually_ge_atTop 1] with M hM
  exact srwHeat_sup_bound hd0 hM x

/-- The walk operator commutes with pointwise limits of functions: if `F M → g`
pointwise, then `walkOp (F M) x → walkOp g x`. -/
lemma tendsto_walkOp {F : ℕ → Site d → ℝ} {g : Site d → ℝ}
    (hF : ∀ y : Site d, Tendsto (fun M : ℕ => F M y) atTop (𝓝 (g y))) (x : Site d) :
    Tendsto (fun M : ℕ => walkOp (F M) x) atTop (𝓝 (walkOp g x)) := by
  have hsum : Tendsto
      (fun M : ℕ => ∑ i : Fin d, (F M (x + unit i) + F M (x - unit i)))
      atTop (𝓝 (∑ i : Fin d, (g (x + unit i) + g (x - unit i)))) :=
    tendsto_finsetSum Finset.univ fun i _ =>
      (hF (x + unit i)).add (hF (x - unit i))
  simpa only [walkOp, nbrSum] using hsum.div_const (2 * (d : ℝ))

/-- If `b(x) = lim_M Σ_{j<M} [P^j(0,0) - P^j(0,x)]` for every `x` and `d ≥ 1`, then
`(P - I) b = 1_{0}`. -/
theorem walkOp_sub_self_of_tendsto (hd : 1 ≤ d) {b : Site d → ℝ}
    (hb : ∀ x, Tendsto (fun M : ℕ => srwGreen d M 0 - srwGreen d M x) atTop (𝓝 (b x)))
    (x : Site d) : walkOp b x - b x = if x = 0 then 1 else 0 := by
  have hlim_walk : Tendsto
      (fun M : ℕ => walkOp (fun y => srwGreen d M 0 - srwGreen d M y) x) atTop
      (𝓝 (walkOp b x)) :=
    tendsto_walkOp (fun y => hb y) x
  have hstep : ∀ M : ℕ,
      walkOp (fun y => srwGreen d M 0 - srwGreen d M y) x
        = (srwGreen d M 0 - srwGreen d M x) + (if x = 0 then 1 else 0)
            - srwHeat d M x := by
    intro M
    have hsub : walkOp (fun y => srwGreen d M 0 - srwGreen d M y) x
        = srwGreen d M 0 - walkOp (srwGreen d M) x := by
      have h := walkOp_sub (fun _ : Site d => srwGreen d M 0) (srwGreen d M) x
      rw [walkOp_const hd] at h
      exact h
    have hwalk : walkOp (srwGreen d M) x
        = ∑ j ∈ Finset.range M, srwHeat d (j + 1) x := by
      have h1 : walkOp (srwGreen d M) x
          = ∑ j ∈ Finset.range M, walkOp (srwHeat d j) x := by
        rw [show srwGreen d M
              = (fun y : Site d => ∑ j ∈ Finset.range M, srwHeat d j y) from rfl]
        exact walkOp_finsetSum _ _ _
      rw [h1]
      exact Finset.sum_congr rfl fun j _ => (srwHeat_succ j x).symm
    have hgreen : (∑ j ∈ Finset.range M, srwHeat d (j + 1) x)
        = srwGreen d (M + 1) x - srwHeat d 0 x := by
      rw [srwGreen, Finset.sum_range_succ']
      ring
    rw [hsub, hwalk, hgreen, srwGreen_succ, srwHeat_zero]
    ring
  have hlim_exp : Tendsto
      (fun M : ℕ => (srwGreen d M 0 - srwGreen d M x) + (if x = 0 then 1 else 0)
        - srwHeat d M x) atTop (𝓝 (b x + (if x = 0 then 1 else 0) - 0)) :=
    ((hb x).add tendsto_const_nhds).sub (tendsto_srwHeat_zero hd x)
  have hlim_walk' : Tendsto
      (fun M : ℕ => (srwGreen d M 0 - srwGreen d M x) + (if x = 0 then 1 else 0)
        - srwHeat d M x) atTop (𝓝 (walkOp b x)) := by
    rw [show (fun M : ℕ => walkOp (fun y => srwGreen d M 0 - srwGreen d M y) x)
          = (fun M : ℕ => (srwGreen d M 0 - srwGreen d M x)
              + (if x = 0 then 1 else 0) - srwHeat d M x)
          from funext fun M => hstep M] at hlim_walk
    exact hlim_walk
  have huniq := tendsto_nhds_unique hlim_walk' hlim_exp
  linarith

/-- For `d ≥ 3` and `b = -G`, `(P - I) b = 1_{0}`. -/
theorem walkOp_neg_srwGreenInf_sub (hd : 3 ≤ d) (x : Site d) :
    walkOp (fun y => -srwGreenInf d y) x - -srwGreenInf d x = if x = 0 then 1 else 0 := by
  rw [walkOp_neg, walkOp_srwGreenInf hd]
  ring

end CERW.Support.LocalTime
