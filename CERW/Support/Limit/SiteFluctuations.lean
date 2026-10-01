import CERW.Support.Statements
import CERW.Support.LocalTime
import CERW.Support.LocalTime.LatticeKernelFacts
import CERW.Support.Main.ScaleLimits
import CERW.Generic.Lattice
import CERW.Generic.Kernel.LogRadial
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellVolume
import LatticeProb.Prob.CramerWold
import LatticeProb.External.PotentialKernelAsymptoticsProved

/-!
# Local times at fixed sites

`thm:site-fluctuations` (Theorem 8.3): the central limit theorem, the law of the iterated
logarithm and the joint limits for the local times `ℓ_n(y)` at fixed sites `y`, from the limit shape
(Theorem 1.1), the fluctuation rates (Theorem 1.2), the fixed-site centering (Lemma 8.2) and the
moment fluctuations (Theorem 8.1), with the martingale central limit theorem and Stout's law of the
iterated logarithm carried as hypotheses.

The Dynkin martingale `M^f` of a combination `f` of translates of the lattice kernel has the
bracket `Σ_x ℓ_n(x) Γ(f, f)(x)` up to an error of order `Σ_{x ∈ A_n} (1 + |x|)^{2-2d}`
(`eq:site-gamma`, `eq:site-bracket`). For `d ≥ 3` the bracket sum is found by dominated
convergence and a summation by parts, which gives `2 G(y - z) - 1_{y = z}`; for `d = 2` it follows
from the planar asymptotics of `Γ` and the planar logarithmic lattice sum. The martingale limit
theorems then give the limits of `M^f`, and the pointwise decomposition of the local time with the
centering and the moment fluctuations show that the remaining potential term is negligible.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Limit

open CERW.Support.Statements

section Helpers

open LatticeProb CERW CERW.Support.Law CERW.Support.LocalTime CERW.Support.Occupation

variable {d : ℕ}

/-- The pointwise bracket `Γ(f, g)(x) = (1/2d) Σ_e (f(x+e) - f(x)) (g(x+e) - g(x))
- Δf(x) Δg(x)` of `eq:site-gamma`, with `Δ = P - I`. -/
private noncomputable def gammaBr (f g : Site d → ℝ) (x : Site d) : ℝ :=
  (1 / (2 * d)) * ∑ e ∈ unitSteps d, (f (x + e) - f x) * (g (x + e) - g x)
    - (walkOp f x - f x) * (walkOp g x - g x)

/-- The combination `x ↦ Σ_i s_i b(x - y_i)` of translates of a kernel `b`. -/
private noncomputable def combo (b : Site d → ℝ) {k : ℕ} (y : Fin k → Site d) (s : Fin k → ℝ)
    (x : Site d) : ℝ :=
  ∑ i, s i * b (x - y i)

/-- The scale `r_n = ((d+1) n / (2 d ε ω_d))^{1/(d+1)}`. -/
private noncomputable def radius (d : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  (((d : ℝ) + 1) * n / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1))

/-- The normalizer `√(r_n log r_n)` (`d = 2`) or `√r_n` (`d ≥ 3`). -/
private noncomputable def sigmaN (d : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  if d = 2 then Real.sqrt (radius d ε n * Real.log (radius d ε n)) else Real.sqrt (radius d ε n)

/-- The law of the iterated logarithm scale. -/
private noncomputable def lilN (d : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  if d = 2 then
    Real.sqrt (2 * radius d ε n * Real.log (radius d ε n) * Real.log (Real.log n))
  else Real.sqrt (2 * radius d ε n * Real.log (Real.log n))

/-- The limiting covariance `cov`. -/
private noncomputable def covN (d : ℕ) (ε : ℝ) (a b : Site d) : ℝ :=
  if d = 2 then 16 * ε / Real.pi
  else 2 * d * ε * (2 * srwGreenInf d (a - b) - if a = b then 1 else 0)

/-- The scale of the negligible terms. -/
private noncomputable def errScale (d : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  Real.log (n + 2) ^ 3 +
    radius d ε n ^ (((3 : ℝ) - d) / 2) * Real.sqrt (Real.log (Real.log n) + 1)

/-! ### Kernel facts -/

/-- The planar lattice kernel is `(2/π) log |x| + κ + O(|x|^{-2})`. -/
private theorem latticeKernel_two_asymp :
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


/-! ### Lattice sums of the bracket -/

/-- The walk operator is the average of `u` over the `2d` unit steps. -/
private theorem gamma_tsum_high_walkOp_eq (u : Site d → ℝ) (x : Site d) :
    walkOp u x = (1 / (2 * d)) * ∑ e ∈ unitSteps d, u (x + e) := by
  rw [sum_unitSteps, walkOp, nbrSum]
  simp only [sub_eq_add_neg]
  ring

/-- `Δu(x) = (1/2d) Σ_e (u(x + e) - u(x))`. -/
private theorem gamma_tsum_high_laplace_eq (hd : 1 ≤ d) (u : Site d → ℝ) (x : Site d) :
    walkOp u x - u x = (1 / (2 * d)) * ∑ e ∈ unitSteps d, (u (x + e) - u x) := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [gamma_tsum_high_walkOp_eq, Finset.sum_sub_distrib, Finset.sum_const, card_unitSteps,
    nsmul_eq_mul]
  push_cast
  field_simp

/-- The pointwise bracket of `f` with itself is `Δ(f²) - 2fΔf - (Δf)²`. -/
private theorem gamma_tsum_high_gammaBr_eq (hd : 1 ≤ d) (f : Site d → ℝ) (x : Site d) :
    gammaBr f f x =
      (walkOp (fun z => f z ^ 2) x - f x ^ 2) - 2 * f x * (walkOp f x - f x)
        - (walkOp f x - f x) ^ 2 := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [gammaBr, gamma_tsum_high_walkOp_eq (fun z => f z ^ 2) x, gamma_tsum_high_walkOp_eq f x]
  have h1 : ∑ e ∈ unitSteps d, (f (x + e) - f x) * (f (x + e) - f x)
      = ∑ e ∈ unitSteps d, f (x + e) ^ 2 - 2 * f x * ∑ e ∈ unitSteps d, f (x + e)
        + 2 * d * f x ^ 2 := by
    have h2 : ∀ e ∈ unitSteps d, (f (x + e) - f x) * (f (x + e) - f x)
        = f (x + e) ^ 2 - 2 * f x * f (x + e) + f x ^ 2 := fun e _ => by ring
    rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, card_unitSteps, nsmul_eq_mul]
    push_cast
    ring
  rw [h1]
  field_simp
  ring

/-- The square of a real power is the power with doubled exponent. -/
private theorem gamma_tsum_high_rpow_sq {t : ℝ} (ht : 0 ≤ t) (p : ℝ) :
    (t ^ p) ^ 2 = t ^ (2 * p) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  push_cast
  ring_nf

/-- A gradient bound gives a bound for the pointwise bracket of `f` with itself. -/
private theorem gamma_tsum_high_abs_gammaBr_le (hd : 1 ≤ d) {f : Site d → ℝ} {C : ℝ}
    (hgrad : ∀ x, ∀ e ∈ unitSteps d,
      |f (x + e) - f x| ≤ C * (1 + euclidNorm x) ^ (1 - (d : ℝ))) (x : Site d) :
    |gammaBr f f x| ≤ 2 * C ^ 2 * (1 + euclidNorm x) ^ (2 - 2 * (d : ℝ)) := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hbase : 0 ≤ 1 + euclidNorm x := by linarith [euclidNorm_nonneg x]
  set m : ℝ := C * (1 + euclidNorm x) ^ (1 - (d : ℝ)) with hm
  have hm2 : m ^ 2 = C ^ 2 * (1 + euclidNorm x) ^ (2 - 2 * (d : ℝ)) := by
    rw [hm, mul_pow, gamma_tsum_high_rpow_sq hbase]
    congr 2
    ring
  have hcard : ((unitSteps d).card : ℝ) = 2 * d := by
    rw [card_unitSteps]
    push_cast
    ring
  have hP0 : 0 ≤ (1 / (2 * d : ℝ)) * ∑ e ∈ unitSteps d, (f (x + e) - f x) * (f (x + e) - f x) := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun e _ => mul_self_nonneg _)
  have hP1 : (1 / (2 * d : ℝ)) * ∑ e ∈ unitSteps d, (f (x + e) - f x) * (f (x + e) - f x)
      ≤ m ^ 2 := by
    have h1 : ∑ e ∈ unitSteps d, (f (x + e) - f x) * (f (x + e) - f x)
        ≤ ∑ _e ∈ unitSteps d, m ^ 2 := by
      refine Finset.sum_le_sum fun e he => ?_
      have := hgrad x e he
      calc (f (x + e) - f x) * (f (x + e) - f x) = |f (x + e) - f x| ^ 2 := by
            rw [sq_abs]; ring
        _ ≤ m ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    rw [Finset.sum_const, nsmul_eq_mul, hcard] at h1
    calc (1 / (2 * d : ℝ)) * ∑ e ∈ unitSteps d, (f (x + e) - f x) * (f (x + e) - f x)
        ≤ (1 / (2 * d : ℝ)) * (2 * d * m ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = m ^ 2 := by field_simp
  have hQ : |walkOp f x - f x| ≤ m := by
    rw [gamma_tsum_high_laplace_eq hd]
    have h1 : |∑ e ∈ unitSteps d, (f (x + e) - f x)| ≤ ∑ _e ∈ unitSteps d, m := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e he => hgrad x e he)
    rw [Finset.sum_const, nsmul_eq_mul, hcard] at h1
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * d))]
    calc (1 / (2 * d : ℝ)) * |∑ e ∈ unitSteps d, (f (x + e) - f x)|
        ≤ (1 / (2 * d : ℝ)) * (2 * d * m) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = m := by field_simp
  have hQ2 : (walkOp f x - f x) * (walkOp f x - f x) ≤ m ^ 2 := by
    calc (walkOp f x - f x) * (walkOp f x - f x) = |walkOp f x - f x| ^ 2 := by
          rw [sq_abs]; ring
      _ ≤ m ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hQ 2
  have hQ0 : 0 ≤ (walkOp f x - f x) * (walkOp f x - f x) := mul_self_nonneg _
  rw [gammaBr, abs_le]
  constructor <;> nlinarith [hm2]

/-- Translating a real power: `(1 + |x - y|)^p ≤ (1 + |y|)^{-p} (1 + |x|)^p` for `p ≤ 0`. -/
private theorem gamma_tsum_high_rpow_translate {p : ℝ} (hp : p ≤ 0) (y x : Site d) :
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

/-- Gradient and decay bounds for a combination of translates of a kernel `b` with
`|∇b(x)| ≲ (1 + |x|)^{1-d}` and `|b(x)| ≲ (1 + |x|)^{2-d}`. -/
private theorem gamma_tsum_high_combo_bounds (hd : 2 ≤ d) {b : Site d → ℝ} {Cg K : ℝ}
    (hCg : 0 ≤ Cg) (hK : 0 ≤ K)
    (hgrad : ∀ x e, e ∈ unitSteps d →
      |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (hdec : ∀ x, |b x| ≤ K * (1 + euclidNorm x) ^ (2 - (d : ℝ))) {k : ℕ}
    (y : Fin k → Site d) (s : Fin k → ℝ) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      (∀ x, ∀ e ∈ unitSteps d, |combo b y s (x + e) - combo b y s x| ≤
        C₁ * (1 + euclidNorm x) ^ (1 - (d : ℝ))) ∧
      ∀ x, |combo b y s x| ≤ C₂ * (1 + euclidNorm x) ^ (2 - (d : ℝ)) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨∑ i, |s i| * (Cg * (1 + euclidNorm (y i)) ^ (-(1 - (d : ℝ)))),
    ∑ i, |s i| * (K * (1 + euclidNorm (y i)) ^ (-(2 - (d : ℝ)))), ?_, ?_, ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _)
      (mul_nonneg hCg (Real.rpow_nonneg (by linarith [euclidNorm_nonneg (y i)]) _))
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _)
      (mul_nonneg hK (Real.rpow_nonneg (by linarith [euclidNorm_nonneg (y i)]) _))
  · intro x e he
    have hsub : combo b y s (x + e) - combo b y s x =
        ∑ i, s i * (b ((x - y i) + e) - b (x - y i)) := by
      simp only [combo, ← Finset.sum_sub_distrib, ← mul_sub]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [add_sub_right_comm]
    rw [hsub, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    have h1 := hgrad (x - y i) e he
    have h2 := gamma_tsum_high_rpow_translate (p := 1 - (d : ℝ)) (by linarith) (y i) x
    calc |s i| * |b ((x - y i) + e) - b (x - y i)|
        ≤ |s i| * (Cg * (1 + euclidNorm (x - y i)) ^ (1 - (d : ℝ))) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ |s i| * (Cg * ((1 + euclidNorm (y i)) ^ (-(1 - (d : ℝ))) *
            (1 + euclidNorm x) ^ (1 - (d : ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hCg) (abs_nonneg _)
      _ = |s i| * (Cg * (1 + euclidNorm (y i)) ^ (-(1 - (d : ℝ)))) *
            (1 + euclidNorm x) ^ (1 - (d : ℝ)) := by ring
  · intro x
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    have h1 := hdec (x - y i)
    have h2 := gamma_tsum_high_rpow_translate (p := 2 - (d : ℝ)) (by linarith) (y i) x
    calc |s i| * |b (x - y i)|
        ≤ |s i| * (K * (1 + euclidNorm (x - y i)) ^ (2 - (d : ℝ))) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ |s i| * (K * ((1 + euclidNorm (y i)) ^ (-(2 - (d : ℝ))) *
            (1 + euclidNorm x) ^ (2 - (d : ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hK) (abs_nonneg _)
      _ = |s i| * (K * (1 + euclidNorm (y i)) ^ (-(2 - (d : ℝ)))) *
            (1 + euclidNorm x) ^ (2 - (d : ℝ)) := by ring

/-- The Green function decays like `(1 + |x|)^{2-d}` for `d ≥ 3`. -/
private theorem gamma_tsum_high_green_decay (hd : 3 ≤ d) :
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

/-- A unit step is nonzero. -/
private theorem gamma_tsum_high_unitStep_ne_zero {e : Site d} (he : e ∈ unitSteps d) :
    e ≠ 0 := by
  obtain ⟨i, rfl | rfl⟩ := mem_unitSteps.mp he
  · exact unit_ne_zero i
  · exact neg_ne_zero.mpr (unit_ne_zero i)

/-- The negative of a unit step is a unit step. -/
private theorem gamma_tsum_high_neg_mem {e : Site d} (he : e ∈ unitSteps d) :
    -e ∈ unitSteps d := by
  obtain ⟨i, rfl | rfl⟩ := mem_unitSteps.mp he
  · exact mem_unitSteps.mpr ⟨i, Or.inr rfl⟩
  · exact mem_unitSteps.mpr ⟨i, Or.inl (neg_neg _)⟩

/-- Every coordinate of a unit step has modulus at most one. -/
private theorem gamma_tsum_high_abs_coord_le {e : Site d} (he : e ∈ unitSteps d) (i : Fin d) :
    |e i| ≤ 1 := by
  obtain ⟨j, rfl | rfl⟩ := mem_unitSteps.mp he
  · simp only [unit, Pi.single_apply]
    split_ifs <;> simp
  · simp only [unit, Pi.neg_apply, Pi.single_apply]
    split_ifs <;> simp

/-- A unit step moves a point of the box of radius `n` into the box of radius `n + 1`. -/
private theorem gamma_tsum_high_add_mem_box {n : ℕ} {x e : Site d}
    (hx : x ∈ boxFinset (0 : Site d) n) (he : e ∈ unitSteps d) :
    x + e ∈ boxFinset (0 : Site d) (n + 1) := by
  rw [mem_boxFinset_zero_iff] at hx ⊢
  rw [supNorm_le_iff] at hx ⊢
  intro i
  have h1 := hx i
  have h2 := gamma_tsum_high_abs_coord_le he i
  rw [Pi.add_apply]
  calc |x i + e i| ≤ |x i| + |e i| := abs_add_le _ _
    _ ≤ (n : ℤ) + 1 := add_le_add h1 h2
    _ = ((n + 1 : ℕ) : ℤ) := by push_cast; ring

/-- The sum of `Δφ` over a finite set is the boundary flux
`(1/2d) Σ_{x ∈ B, e, x + e ∉ B} (φ(x + e) - φ(x))`. -/
private theorem gamma_tsum_high_sum_laplace (hd : 1 ≤ d) (B : Finset (Site d))
    (φ : Site d → ℝ) :
    ∑ x ∈ B, (walkOp φ x - φ x) =
      (1 / (2 * d)) * ∑ p ∈ (B ×ˢ unitSteps d).filter (fun p => p.1 + p.2 ∉ B),
        (φ (p.1 + p.2) - φ p.1) := by
  have h1 : ∑ x ∈ B, (walkOp φ x - φ x) =
      (1 / (2 * d)) * ∑ p ∈ B ×ˢ unitSteps d, (φ (p.1 + p.2) - φ p.1) := by
    rw [Finset.sum_product, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => gamma_tsum_high_laplace_eq hd φ x
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
      exact gamma_tsum_high_unitStep_ne_zero he (by simpa using h2)
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hx := (Finset.mem_product.mp hp'.1).1
      have he := (Finset.mem_product.mp hp'.1).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp'.2, ?_⟩, ?_⟩
      · exact gamma_tsum_high_neg_mem he
      · simpa using hx
    · intro p _
      simp
  rw [h0, zero_add]

/-- The boundary pairs of the box of radius `n + 1` have first coordinate in the outer shell. -/
private theorem gamma_tsum_high_bdry_subset (n : ℕ) :
    (boxFinset (0 : Site d) (n + 1) ×ˢ unitSteps d).filter
        (fun p => p.1 + p.2 ∉ boxFinset (0 : Site d) (n + 1)) ⊆
      (boxFinset (0 : Site d) (n + 1) \ boxFinset (0 : Site d) n) ×ˢ unitSteps d := by
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
  obtain ⟨hx, he⟩ := Finset.mem_product.mp hp1
  refine Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨hx, fun hn => hp2 ?_⟩, he⟩
  exact gamma_tsum_high_add_mem_box hn he

/-- The flux of `Δφ` through the box of radius `n + 1` is small when `φ` has a gradient bound
`(1 + |x|)^{3-2d}`. -/
private theorem gamma_tsum_high_flux_bound (hd : 3 ≤ d) {φ : Site d → ℝ} {Cφ : ℝ}
    (hCφ : 0 ≤ Cφ)
    (hφ : ∀ x, ∀ e ∈ unitSteps d,
      |φ (x + e) - φ x| ≤ Cφ * (1 + euclidNorm x) ^ (3 - 2 * (d : ℝ))) (n : ℕ) :
    |∑ x ∈ boxFinset (0 : Site d) (n + 1), (walkOp φ x - φ x)| ≤
      2 * d * 2 ^ (d - 1) * Cφ * ((n : ℝ) + 2) ^ (2 - (d : ℝ)) := by
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  set B := boxFinset (0 : Site d) (n + 1) with hB
  set bd := (B ×ˢ unitSteps d).filter (fun p => p.1 + p.2 ∉ B) with hbd
  have hbound : ∀ p ∈ bd, |φ (p.1 + p.2) - φ p.1| ≤
      Cφ * ((n : ℝ) + 2) ^ (3 - 2 * (d : ℝ)) := by
    intro p hp
    have hsub := gamma_tsum_high_bdry_subset (d := d) n hp
    obtain ⟨hx, he⟩ := Finset.mem_product.mp hsub
    have hsn : supNorm p.1 = n + 1 := supNorm_eq_of_mem_sdiff hx
    have hnorm : ((n : ℝ) + 1) ≤ euclidNorm p.1 := by
      have := supNorm_le_euclidNorm p.1
      rw [hsn] at this
      push_cast at this
      exact this
    have h1 := hφ p.1 p.2 he
    have h2 : (1 + euclidNorm p.1) ^ (3 - 2 * (d : ℝ)) ≤ ((n : ℝ) + 2) ^ (3 - 2 * (d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hn2 (by linarith) (by
        have : (3 : ℝ) ≤ d := by exact_mod_cast hd
        linarith)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hCφ)
  have hcard : (bd.card : ℝ) ≤ (shellCard d (n + 1) : ℝ) * (2 * d) := by
    have h1 := Finset.card_le_card (gamma_tsum_high_bdry_subset (d := d) n)
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
  have hpow : ((n : ℝ) + 2) ^ (d - 1) * ((n : ℝ) + 2) ^ (3 - 2 * (d : ℝ)) =
      ((n : ℝ) + 2) ^ (2 - (d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn2]
    congr 1
    rw [Nat.cast_sub hd1]
    push_cast
    ring
  rw [gamma_tsum_high_sum_laplace hd1, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * d))]
  have hsum : |∑ p ∈ bd, (φ (p.1 + p.2) - φ p.1)| ≤
      bd.card * (Cφ * ((n : ℝ) + 2) ^ (3 - 2 * (d : ℝ))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ p ∈ bd, |φ (p.1 + p.2) - φ p.1|
        ≤ ∑ _p ∈ bd, Cφ * ((n : ℝ) + 2) ^ (3 - 2 * (d : ℝ)) := Finset.sum_le_sum hbound
      _ = bd.card * (Cφ * ((n : ℝ) + 2) ^ (3 - 2 * (d : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hW : 0 ≤ Cφ * ((n : ℝ) + 2) ^ (3 - 2 * (d : ℝ)) :=
    mul_nonneg hCφ (Real.rpow_nonneg hn2.le _)
  calc (1 / (2 * d : ℝ)) * |∑ p ∈ bd, (φ (p.1 + p.2) - φ p.1)|
      ≤ (1 / (2 * d : ℝ)) * (bd.card * (Cφ * ((n : ℝ) + 2) ^ (3 - 2 * (d : ℝ)))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (1 / (2 * d : ℝ)) * ((shellCard d (n + 1) : ℝ) * (2 * d) *
          (Cφ * ((n : ℝ) + 2) ^ (3 - 2 * (d : ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hW) (by positivity)
    _ = (shellCard d (n + 1) : ℝ) * (Cφ * ((n : ℝ) + 2) ^ (3 - 2 * (d : ℝ))) := by
        field_simp
    _ ≤ (2 * d * 2 ^ (d - 1) * ((n : ℝ) + 2) ^ (d - 1)) *
          (Cφ * ((n : ℝ) + 2) ^ (3 - 2 * (d : ℝ))) := mul_le_mul_of_nonneg_right hshell hW
    _ = 2 * d * 2 ^ (d - 1) * Cφ * (((n : ℝ) + 2) ^ (d - 1) *
          ((n : ℝ) + 2) ^ (3 - 2 * (d : ℝ))) := by ring
    _ = 2 * d * 2 ^ (d - 1) * Cφ * ((n : ℝ) + 2) ^ (2 - (d : ℝ)) := by rw [hpow]

/-- `(n + 2)^{2-d} → 0` for `d ≥ 3`. -/
private theorem gamma_tsum_high_tendsto_rpow (hd : 3 ≤ d) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) ^ (2 - (d : ℝ))) atTop (𝓝 0) := by
  have hd2 : (2 : ℝ) < d := by exact_mod_cast (by omega : 2 < d)
  have h1 := (tendsto_rpow_neg_atTop (y := (d : ℝ) - 2) (by linarith)).comp
    (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  refine h1.congr fun n => ?_
  simp only [Function.comp_apply, neg_sub]

/-- The square of a function with gradient and decay bounds has gradient bound
`(1 + |x|)^{3-2d}`. -/
private theorem gamma_tsum_high_square_grad {f : Site d → ℝ} {C₁ C₂ : ℝ}
    (hgrad : ∀ x, ∀ e ∈ unitSteps d,
      |f (x + e) - f x| ≤ C₁ * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (hdec : ∀ x, |f x| ≤ C₂ * (1 + euclidNorm x) ^ (2 - (d : ℝ))) (hd : 2 ≤ d) :
    ∀ x, ∀ e ∈ unitSteps d, |(fun z => f z ^ 2) (x + e) - (fun z => f z ^ 2) x| ≤
      (C₁ ^ 2 + 2 * C₂ * C₁) * (1 + euclidNorm x) ^ (3 - 2 * (d : ℝ)) := by
  intro x e he
  have hbase : 1 ≤ 1 + euclidNorm x := by linarith [euclidNorm_nonneg x]
  have hb0 : 0 ≤ 1 + euclidNorm x := by linarith
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 := hgrad x e he
  have h2 := hdec x
  have hid : (f (x + e) ^ 2 - f x ^ 2) =
      (f (x + e) - f x) * (f (x + e) - f x) + 2 * f x * (f (x + e) - f x) := by ring
  have hsq : (1 + euclidNorm x) ^ (1 - (d : ℝ)) * (1 + euclidNorm x) ^ (1 - (d : ℝ)) =
      (1 + euclidNorm x) ^ (2 - 2 * (d : ℝ)) := by
    rw [← Real.rpow_add (by linarith)]
    congr 1
    ring
  have hmix : (1 + euclidNorm x) ^ (2 - (d : ℝ)) * (1 + euclidNorm x) ^ (1 - (d : ℝ)) =
      (1 + euclidNorm x) ^ (3 - 2 * (d : ℝ)) := by
    rw [← Real.rpow_add (by linarith)]
    congr 1
    ring
  have hle : (1 + euclidNorm x) ^ (2 - 2 * (d : ℝ)) ≤ (1 + euclidNorm x) ^ (3 - 2 * (d : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have hA : |(f (x + e) - f x) * (f (x + e) - f x)| ≤
      C₁ ^ 2 * (1 + euclidNorm x) ^ (3 - 2 * (d : ℝ)) := by
    rw [abs_mul]
    calc |f (x + e) - f x| * |f (x + e) - f x|
        ≤ (C₁ * (1 + euclidNorm x) ^ (1 - (d : ℝ))) *
            (C₁ * (1 + euclidNorm x) ^ (1 - (d : ℝ))) :=
          mul_le_mul h1 h1 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
      _ = C₁ ^ 2 * (1 + euclidNorm x) ^ (2 - 2 * (d : ℝ)) := by rw [← hsq]; ring
      _ ≤ C₁ ^ 2 * (1 + euclidNorm x) ^ (3 - 2 * (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hle (sq_nonneg _)
  have hB : |2 * f x * (f (x + e) - f x)| ≤
      2 * C₂ * C₁ * (1 + euclidNorm x) ^ (3 - 2 * (d : ℝ)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc 2 * |f x| * |f (x + e) - f x|
        ≤ 2 * (C₂ * (1 + euclidNorm x) ^ (2 - (d : ℝ))) *
            (C₁ * (1 + euclidNorm x) ^ (1 - (d : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) h1 (abs_nonneg _)
            (by have := le_trans (abs_nonneg _) h2; linarith)
      _ = 2 * C₂ * C₁ * ((1 + euclidNorm x) ^ (2 - (d : ℝ)) *
            (1 + euclidNorm x) ^ (1 - (d : ℝ))) := by ring
      _ = 2 * C₂ * C₁ * (1 + euclidNorm x) ^ (3 - 2 * (d : ℝ)) := by rw [hmix]
  show |f (x + e) ^ 2 - f x ^ 2| ≤ _
  rw [hid]
  calc |(f (x + e) - f x) * (f (x + e) - f x) + 2 * f x * (f (x + e) - f x)|
      ≤ |(f (x + e) - f x) * (f (x + e) - f x)| + |2 * f x * (f (x + e) - f x)| :=
        abs_add_le _ _
    _ ≤ C₁ ^ 2 * (1 + euclidNorm x) ^ (3 - 2 * (d : ℝ)) +
        2 * C₂ * C₁ * (1 + euclidNorm x) ^ (3 - 2 * (d : ℝ)) := add_le_add hA hB
    _ = (C₁ ^ 2 + 2 * C₂ * C₁) * (1 + euclidNorm x) ^ (3 - 2 * (d : ℝ)) := by ring

/-- Summation of the bracket of a decaying function whose Laplacian has finite support: the
total is minus the sum over the support of `2 f Δf + (Δf)²`. -/
private theorem gamma_tsum_high_abstract (hd : 3 ≤ d) {f : Site d → ℝ} {C₁ C₂ : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hgrad : ∀ x, ∀ e ∈ unitSteps d,
      |f (x + e) - f x| ≤ C₁ * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (hdec : ∀ x, |f x| ≤ C₂ * (1 + euclidNorm x) ^ (2 - (d : ℝ)))
    (T : Finset (Site d)) (hT : ∀ x ∉ T, walkOp f x - f x = 0) :
    Summable (fun x => gammaBr f f x) ∧
      ∑' x, gammaBr f f x =
        -∑ x ∈ T, (2 * f x * (walkOp f x - f x) + (walkOp f x - f x) ^ 2) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (d : ℝ) < 2 * (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsum : Summable (fun x => gammaBr f f x) := by
    refine Summable.of_norm_bounded ((summable_one_add_euclidNorm_rpow d hd2).mul_left
      (2 * C₁ ^ 2)) fun x => ?_
    rw [Real.norm_eq_abs]
    refine (gamma_tsum_high_abs_gammaBr_le hd1 hgrad x).trans (le_of_eq ?_)
    congr 2
    ring
  refine ⟨hsum, ?_⟩
  set g : Site d → ℝ := fun x =>
    2 * f x * (walkOp f x - f x) + (walkOp f x - f x) ^ 2 with hg
  set V : ℝ := ∑ x ∈ T, g x with hV
  set φ : Site d → ℝ := fun z => f z ^ 2 with hφ
  have hpoint : ∀ x, gammaBr f f x = (walkOp φ x - φ x) - g x := by
    intro x
    rw [gamma_tsum_high_gammaBr_eq hd1, hg]
    ring
  have hφgrad := gamma_tsum_high_square_grad hgrad hdec (by omega)
  have hCφ : 0 ≤ C₁ ^ 2 + 2 * C₂ * C₁ := by positivity
  set N₀ : ℕ := T.sup supNorm with hN₀
  have hTbox : ∀ n : ℕ, N₀ ≤ n + 1 → T ⊆ boxFinset (0 : Site d) (n + 1) := by
    intro n hn x hx
    rw [mem_boxFinset_zero_iff]
    exact (Finset.le_sup (f := supNorm) hx).trans hn
  have hfinite : ∀ n : ℕ, N₀ ≤ n + 1 →
      ∑ x ∈ boxFinset (0 : Site d) (n + 1), gammaBr f f x =
        ∑ x ∈ boxFinset (0 : Site d) (n + 1), (walkOp φ x - φ x) - V := by
    intro n hn
    have h1 : ∑ x ∈ boxFinset (0 : Site d) (n + 1), g x = V := by
      rw [hV]
      refine (Finset.sum_subset (hTbox n hn) fun x _ hxT => ?_).symm
      simp only [hg, hT x hxT]
      ring
    rw [Finset.sum_congr rfl fun x _ => hpoint x, Finset.sum_sub_distrib, h1]
  have hexh : Tendsto (fun n : ℕ => boxFinset (0 : Site d) (n + 1)) atTop atTop := by
    refine tendsto_atTop_finset_of_monotone (fun m n hmn => ?_) fun x => ⟨supNorm x, ?_⟩
    · exact boxFinset_zero_subset (by omega)
    · rw [mem_boxFinset_zero_iff]
      omega
  have hlim1 : Tendsto (fun n : ℕ => ∑ x ∈ boxFinset (0 : Site d) (n + 1), gammaBr f f x)
      atTop (𝓝 (∑' x, gammaBr f f x)) := by
    have h : HasSum (fun x => gammaBr f f x) (∑' x, gammaBr f f x) := hsum.hasSum
    exact h.comp hexh
  have hlim2 : Tendsto (fun n : ℕ => ∑ x ∈ boxFinset (0 : Site d) (n + 1), gammaBr f f x)
      atTop (𝓝 (-V)) := by
    have hz : Tendsto (fun n : ℕ => ∑ x ∈ boxFinset (0 : Site d) (n + 1), gammaBr f f x + V)
        atTop (𝓝 0) := by
      have hconst := (gamma_tsum_high_tendsto_rpow hd).const_mul
        (2 * d * 2 ^ (d - 1) * (C₁ ^ 2 + 2 * C₂ * C₁))
      rw [mul_zero] at hconst
      refine squeeze_zero_norm' ?_ hconst
      filter_upwards [eventually_ge_atTop N₀] with n hn
      rw [hfinite n (by omega), sub_add_cancel, Real.norm_eq_abs]
      exact gamma_tsum_high_flux_bound hd hCφ hφgrad n
    have := hz.sub_const V
    simpa using this
  exact tendsto_nhds_unique hlim1 hlim2

/-- The Laplacian of a combination of translates of a kernel `b` with `(P - I) b = 1_{0}`. -/
private theorem gamma_tsum_high_combo_laplace {b : Site d → ℝ}
    (hb : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0) {k : ℕ} (y : Fin k → Site d)
    (s : Fin k → ℝ) (x : Site d) :
    walkOp (combo b y s) x - combo b y s x = ∑ i, s i * (if x = y i then 1 else 0) := by
  have hlin : walkOp (combo b y s) x = ∑ i, s i * walkOp b (x - y i) := by
    rw [gamma_tsum_high_walkOp_eq]
    simp only [combo]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gamma_tsum_high_walkOp_eq b (x - y i)]
    simp only [add_sub_right_comm]
    rw [← Finset.mul_sum]
    ring
  rw [hlin]
  simp only [combo, ← Finset.sum_sub_distrib, ← mul_sub]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hb (x - y i)]
  simp only [sub_eq_zero]

/-- `Σ_x Γ` for `d ≥ 3`. -/
private theorem gamma_tsum_high (hd : 3 ≤ d) {k : ℕ} (y : Fin k → Site d) (s : Fin k → ℝ) :
    Summable (fun x => gammaBr (combo (latticeKernel d) y s) (combo (latticeKernel d) y s) x) ∧
    ∑' x, gammaBr (combo (latticeKernel d) y s) (combo (latticeKernel d) y s) x =
      ∑ i, ∑ j, s i * s j * (2 * srwGreenInf d (y i - y j) - if y i = y j then 1 else 0) := by
  obtain ⟨h, hK⟩ := exists_kernelFacts_latticeKernel (d := d) (by omega)
  obtain ⟨Cg, hgrad⟩ := hK.gradBound
  obtain ⟨K, hK0, hdec⟩ := gamma_tsum_high_green_decay hd
  have hgrad' : ∀ x e, e ∈ unitSteps d → |latticeKernel d (x + e) - latticeKernel d x| ≤
      |Cg| * (1 + euclidNorm x) ^ (1 - (d : ℝ)) := fun x e he =>
    (hgrad x e he).trans (mul_le_mul_of_nonneg_right (le_abs_self _)
      (Real.rpow_nonneg (by linarith [euclidNorm_nonneg x]) _))
  obtain ⟨C₁, C₂, hC₁, hC₂, hg1, hg2⟩ :=
    gamma_tsum_high_combo_bounds (by omega) (abs_nonneg Cg) hK0 hgrad' hdec y s
  have hpois := gamma_tsum_high_combo_laplace hK.poisson y s
  set f := combo (latticeKernel d) y s with hf
  have hT : ∀ x ∉ Finset.univ.image y, walkOp f x - f x = 0 := by
    intro x hx
    rw [hpois x]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : x ≠ y i := fun hxi => hx (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hxi.symm⟩)
    simp [this]
  obtain ⟨hsum, hval⟩ := gamma_tsum_high_abstract hd hC₁ hC₂ hg1 hg2 (Finset.univ.image y) hT
  refine ⟨hsum, ?_⟩
  rw [hval]
  have hmem : ∀ i, y i ∈ Finset.univ.image y := fun i =>
    Finset.mem_image_of_mem y (Finset.mem_univ i)
  have hV1 : ∑ x ∈ Finset.univ.image y, 2 * f x * (walkOp f x - f x) =
      2 * ∑ i, s i * f (y i) := by
    have h1 : ∀ x ∈ Finset.univ.image y, 2 * f x * (walkOp f x - f x) =
        ∑ i, (if x = y i then 2 * (s i * f x) else 0) := by
      intro x _
      rw [hpois x, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> ring
    rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq' (Finset.univ.image y) (y i) (fun x => 2 * (s i * f x)), if_pos (hmem i)]
  have hV2 : ∑ x ∈ Finset.univ.image y, (walkOp f x - f x) ^ 2 =
      ∑ i, ∑ j, s i * s j * (if y i = y j then 1 else 0) := by
    have h1 : ∀ x ∈ Finset.univ.image y, (walkOp f x - f x) ^ 2 =
        ∑ i, ∑ j, (if x = y i then s i * s j * (if y i = y j then 1 else 0) else 0) := by
      intro x _
      rw [hpois x, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases hxi : x = y i
      · subst hxi
        by_cases hij : y i = y j <;> simp [hij]
      · rw [if_neg hxi]
        simp [hxi]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_ite_eq' (Finset.univ.image y) (y i)
      (fun x => s i * s j * (if y i = y j then 1 else 0)), if_pos (hmem i)]
  have hfy : ∀ i, f (y i) = -∑ j, s j * srwGreenInf d (y i - y j) := by
    intro i
    simp only [hf, combo, latticeKernel, if_neg (show d ≠ 2 by omega)]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e1 : ∑ i, s i * -∑ j, s j * srwGreenInf d (y i - y j) =
      -∑ i, ∑ j, s i * s j * srwGreenInf d (y i - y j) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_neg, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ i, ∑ j, s i * s j *
      (2 * srwGreenInf d (y i - y j) - if y i = y j then 1 else 0) =
      2 * ∑ i, ∑ j, s i * s j * srwGreenInf d (y i - y j) -
        ∑ i, ∑ j, s i * s j * (if y i = y j then 1 else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_add_distrib, hV1, hV2]
  simp only [hfy]
  rw [e1, e2]
  ring


/-! ### The planar logarithmic lattice sum -/

/-- The summand `(euclidNorm x ^ 2)⁻¹` is the real power `euclidNorm x ^ (-2)`. -/
private lemma euclidNorm_rpow_neg_two (x : Site 2) :
    euclidNorm x ^ (-(2 : ℝ)) = (euclidNorm x ^ 2)⁻¹ := by
  rw [Real.rpow_neg (euclidNorm_nonneg x),
    show euclidNorm x ^ (2 : ℝ) = euclidNorm x ^ 2 from Real.rpow_natCast _ 2]

/-! ### The increments of the planar kernel -/

/-- The real dot product `e · w` of two lattice sites in the plane. -/
private noncomputable def gamma_ball_sum_planar_dot (e w : Site 2) : ℝ :=
  ∑ j : Fin 2, ((e j : ℤ) : ℝ) * ((w j : ℤ) : ℝ)

/-- The squared norm of a planar site is the sum of its two squared coordinates. -/
private lemma gamma_ball_sum_planar_norm_sq (w : Site 2) :
    euclidNorm w ^ 2 = ((w 0 : ℤ) : ℝ) ^ 2 + ((w 1 : ℤ) : ℝ) ^ 2 := by
  rw [euclidNorm_sq_eq_sum, Fin.sum_univ_two]

/-- Stepping by a unit vector `e` changes the squared norm by `2 e · w + 1`. -/
private lemma gamma_ball_sum_planar_norm_add_sq {e : Site 2} (he : e ∈ unitSteps 2)
    (w : Site 2) :
    euclidNorm (w + e) ^ 2 = euclidNorm w ^ 2 + 2 * gamma_ball_sum_planar_dot e w + 1 := by
  have h1 : euclidNorm e ^ 2 = 1 := by rw [euclidNorm_of_mem_unitSteps he]; norm_num
  rw [gamma_ball_sum_planar_norm_sq] at h1
  rw [gamma_ball_sum_planar_norm_sq, gamma_ball_sum_planar_norm_sq, gamma_ball_sum_planar_dot,
    Fin.sum_univ_two]
  simp only [Pi.add_apply, Int.cast_add]
  linarith

/-- The dot product of a unit vector with `w` is at most `|w|` in absolute value. -/
private lemma gamma_ball_sum_planar_abs_dot_le {e : Site 2} (he : e ∈ unitSteps 2) (w : Site 2) :
    |gamma_ball_sum_planar_dot e w| ≤ euclidNorm w := by
  have h1 : euclidNorm e ^ 2 = 1 := by rw [euclidNorm_of_mem_unitSteps he]; norm_num
  rw [gamma_ball_sum_planar_norm_sq] at h1
  rw [euclidNorm]
  apply Real.abs_le_sqrt
  rw [gamma_ball_sum_planar_dot, Fin.sum_univ_two]
  simp only [Fin.sum_univ_two]
  nlinarith [sq_nonneg (((e 0 : ℤ) : ℝ) * ((w 1 : ℤ) : ℝ) - ((e 1 : ℤ) : ℝ) * ((w 0 : ℤ) : ℝ))]

/-- The logarithm of the norm after a unit step, to second order:
`|log|w + e| - log|w| - (e · w)/|w|²| ≤ 10/|w|²` for `|w| ≥ 6`. -/
private lemma gamma_ball_sum_planar_log_step {e : Site 2} (he : e ∈ unitSteps 2) {w : Site 2}
    (hw : 6 ≤ euclidNorm w) :
    |Real.log (euclidNorm (w + e)) - Real.log (euclidNorm w) -
        gamma_ball_sum_planar_dot e w / euclidNorm w ^ 2| ≤ 10 / euclidNorm w ^ 2 := by
  set ρ := euclidNorm w with hρ
  set δ := gamma_ball_sum_planar_dot e w with hδ
  have hρpos : 0 < ρ := by linarith
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hsq := gamma_ball_sum_planar_norm_add_sq he w
  have hδle : |δ| ≤ ρ := gamma_ball_sum_planar_abs_dot_le he w
  set t : ℝ := (2 * δ + 1) / ρ ^ 2 with ht
  have hρ'2 : euclidNorm (w + e) ^ 2 = ρ ^ 2 * (1 + t) := by
    rw [hsq, ht]
    field_simp
    ring
  have hδ1 : |2 * δ + 1| ≤ 3 * ρ := by
    calc |2 * δ + 1| ≤ |2 * δ| + |(1 : ℝ)| := abs_add_le _ _
      _ = 2 * |δ| + 1 := by rw [abs_mul, abs_one]; norm_num
      _ ≤ 3 * ρ := by linarith
  have htabs : |t| ≤ 3 / ρ := by
    rw [ht, abs_div, abs_of_pos hρ2, div_le_div_iff₀ hρ2 hρpos]
    calc |2 * δ + 1| * ρ ≤ 3 * ρ * ρ := mul_le_mul_of_nonneg_right hδ1 hρpos.le
      _ = 3 * ρ ^ 2 := by ring
  have hthalf : |t| ≤ 1 / 2 := by
    refine htabs.trans ?_
    rw [div_le_div_iff₀ hρpos (by norm_num)]
    linarith
  have hpos1t : 0 < 1 + t := by
    have := (abs_le.mp hthalf).1
    linarith
  have hρ'pos : 0 < euclidNorm (w + e) := by
    have h2 : 0 < euclidNorm (w + e) ^ 2 := by rw [hρ'2]; positivity
    refine lt_of_le_of_ne (euclidNorm_nonneg _) fun h => ?_
    rw [← h] at h2
    simp at h2
  have hlogsq : 2 * Real.log (euclidNorm (w + e)) =
      2 * Real.log ρ + Real.log (1 + t) := by
    have e1 : Real.log (euclidNorm (w + e) ^ 2) = 2 * Real.log (euclidNorm (w + e)) := by
      simp
    have e2 : Real.log (ρ ^ 2) = 2 * Real.log ρ := by simp
    rw [← e1, hρ'2, Real.log_mul hρ2.ne' hpos1t.ne', e2]
  have hT := CERW.Generic.Kernel.abs_log_one_add_sub_le hthalf
  have ht2 : t ^ 2 ≤ 9 / ρ ^ 2 := by
    have : t ^ 2 ≤ (3 / ρ) ^ 2 := by
      rw [← sq_abs t]
      exact pow_le_pow_left₀ (abs_nonneg t) htabs 2
    calc t ^ 2 ≤ (3 / ρ) ^ 2 := this
      _ = 9 / ρ ^ 2 := by rw [div_pow]; norm_num
  have hkey : Real.log (euclidNorm (w + e)) - Real.log ρ - δ / ρ ^ 2 =
      (Real.log (1 + t) - t) / 2 + 1 / (2 * ρ ^ 2) := by
    have h2 : Real.log (euclidNorm (w + e)) - Real.log ρ = Real.log (1 + t) / 2 := by
      linarith
    rw [h2, ht]
    field_simp
    ring
  rw [hkey]
  have h1 : |(Real.log (1 + t) - t) / 2| ≤ 9 / ρ ^ 2 := by
    rw [abs_div, abs_two]
    calc |Real.log (1 + t) - t| / 2 ≤ 2 * t ^ 2 / 2 := by gcongr
      _ = t ^ 2 := by ring
      _ ≤ 9 / ρ ^ 2 := ht2
  have h2 : |1 / (2 * ρ ^ 2)| ≤ 1 / ρ ^ 2 := by
    rw [abs_of_pos (by positivity)]
    apply one_div_le_one_div_of_le hρ2
    nlinarith
  calc |(Real.log (1 + t) - t) / 2 + 1 / (2 * ρ ^ 2)|
      ≤ |(Real.log (1 + t) - t) / 2| + |1 / (2 * ρ ^ 2)| := abs_add_le _ _
    _ ≤ 9 / ρ ^ 2 + 1 / ρ ^ 2 := add_le_add h1 h2
    _ = 10 / ρ ^ 2 := by ring

/-- The increments of the planar kernel:
`b(w + e) - b(w) = (2/π) (e · w)/|w|² + O(|w|^{-2})` for unit steps `e`. -/
private theorem gamma_ball_sum_planar_increment :
    ∃ K R : ℝ, 0 ≤ K ∧ 1 ≤ R ∧ ∀ (w e : Site 2), e ∈ unitSteps 2 → R ≤ euclidNorm w →
      |latticeKernel 2 (w + e) - latticeKernel 2 w -
        2 / Real.pi * (gamma_ball_sum_planar_dot e w / euclidNorm w ^ 2)| ≤
          K / euclidNorm w ^ 2 := by
  obtain ⟨κ, C, R₀, hR₀, hasymp⟩ := latticeKernel_two_asymp
  refine ⟨5 * max C 0 + 20 / Real.pi, R₀ + 6, by positivity, by linarith, ?_⟩
  intro w e he hw
  have hρ6 : 6 ≤ euclidNorm w := by linarith
  have hlog := gamma_ball_sum_planar_log_step he hρ6
  have h0 := hasymp w (by linarith)
  have hρ'ge : euclidNorm w - 1 ≤ euclidNorm (w + e) := by
    have h := euclidNorm_sub_le (w + e) e
    rw [add_sub_cancel_right, euclidNorm_of_mem_unitSteps he] at h
    linarith
  have h1 := hasymp (w + e) (by linarith)
  rw [euclidNorm_rpow_neg_two] at h0 h1
  set ρ := euclidNorm w with hρ
  set ρ' := euclidNorm (w + e) with hρ'
  set δ := gamma_ball_sum_planar_dot e w with hδ
  have hρpos : 0 < ρ := by linarith
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hC : 0 ≤ max C 0 := le_max_right _ _
  have hCle : C ≤ max C 0 := le_max_left _ _
  have hρ'sq : ρ ^ 2 / 4 ≤ ρ' ^ 2 := by nlinarith
  have hinv : (ρ' ^ 2)⁻¹ ≤ 4 / ρ ^ 2 := by
    have hpos : 0 < ρ ^ 2 / 4 := by positivity
    calc (ρ' ^ 2)⁻¹ ≤ (ρ ^ 2 / 4)⁻¹ := inv_anti₀ hpos hρ'sq
      _ = 4 / ρ ^ 2 := by rw [inv_div]
  have hb1 : |latticeKernel 2 (w + e) - (2 / Real.pi * Real.log ρ' + κ)| ≤
      max C 0 * (4 / ρ ^ 2) :=
    h1.trans ((mul_le_mul_of_nonneg_right hCle (inv_nonneg.mpr (sq_nonneg _))).trans
      (mul_le_mul_of_nonneg_left hinv hC))
  have hb0 : |latticeKernel 2 w - (2 / Real.pi * Real.log ρ + κ)| ≤ max C 0 * (1 / ρ ^ 2) := by
    refine h0.trans ?_
    rw [← one_div]
    exact mul_le_mul_of_nonneg_right hCle (by positivity)
  have hpi : 0 < 2 / Real.pi := by positivity
  have hdecomp : latticeKernel 2 (w + e) - latticeKernel 2 w - 2 / Real.pi * (δ / ρ ^ 2) =
      (latticeKernel 2 (w + e) - (2 / Real.pi * Real.log ρ' + κ)) -
        (latticeKernel 2 w - (2 / Real.pi * Real.log ρ + κ)) +
        2 / Real.pi * (Real.log ρ' - Real.log ρ - δ / ρ ^ 2) := by ring
  rw [hdecomp]
  have hl : |2 / Real.pi * (Real.log ρ' - Real.log ρ - δ / ρ ^ 2)| ≤
      2 / Real.pi * (10 / ρ ^ 2) := by
    rw [abs_mul, abs_of_pos hpi]
    exact mul_le_mul_of_nonneg_left hlog hpi.le
  calc |(latticeKernel 2 (w + e) - (2 / Real.pi * Real.log ρ' + κ)) -
        (latticeKernel 2 w - (2 / Real.pi * Real.log ρ + κ)) +
        2 / Real.pi * (Real.log ρ' - Real.log ρ - δ / ρ ^ 2)|
      ≤ |(latticeKernel 2 (w + e) - (2 / Real.pi * Real.log ρ' + κ)) -
        (latticeKernel 2 w - (2 / Real.pi * Real.log ρ + κ))| +
        |2 / Real.pi * (Real.log ρ' - Real.log ρ - δ / ρ ^ 2)| := abs_add_le _ _
    _ ≤ (|latticeKernel 2 (w + e) - (2 / Real.pi * Real.log ρ' + κ)| +
        |latticeKernel 2 w - (2 / Real.pi * Real.log ρ + κ)|) +
        2 / Real.pi * (10 / ρ ^ 2) := add_le_add (abs_sub _ _) hl
    _ ≤ (max C 0 * (4 / ρ ^ 2) + max C 0 * (1 / ρ ^ 2)) + 2 / Real.pi * (10 / ρ ^ 2) :=
        add_le_add (add_le_add hb1 hb0) le_rfl
    _ = (5 * max C 0 + 20 / Real.pi) / ρ ^ 2 := by
        field_simp
        ring

/-- Translating the base point by `y` moves `a/σ²` to `(a - b)/ρ²`-type terms by `O(η/ρ²)`:
the real-number form of the comparison of `(e · (x - y))/|x - y|²` with `(e · x)/|x|²`. -/
private lemma gamma_ball_sum_planar_translate_real {a b p ρ σ η : ℝ} (hρ : 0 < ρ) (hη : 0 ≤ η)
    (hησ : 2 * η ≤ ρ) (ha : |a| ≤ ρ) (hb : |b| ≤ η) (hp : |p| ≤ ρ * η)
    (hσ : σ = ρ ^ 2 - 2 * p + η ^ 2) :
    |(a - b) / σ - a / ρ ^ 2| ≤ 16 * η / ρ ^ 2 := by
  have hσlow : ρ ^ 2 / 4 ≤ σ := by
    have hp' := (abs_le.mp hp).2
    have : (ρ - η) ^ 2 ≤ σ := by rw [hσ]; nlinarith
    nlinarith
  have hσpos : 0 < σ := lt_of_lt_of_le (by positivity) hσlow
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hnum : (a - b) / σ - a / ρ ^ 2 = (a * (2 * p - η ^ 2) - b * ρ ^ 2) / (σ * ρ ^ 2) := by
    field_simp
    rw [hσ]
    ring
  rw [hnum, abs_div, abs_of_pos (mul_pos hσpos hρ2), div_le_div_iff₀ (mul_pos hσpos hρ2) hρ2]
  have haρ := abs_le.mp ha
  have hbη := abs_le.mp hb
  have hpρη := abs_le.mp hp
  have h1 : |a * (2 * p - η ^ 2) - b * ρ ^ 2| ≤ 4 * ρ ^ 2 * η := by
    have hA : |a * (2 * p - η ^ 2)| ≤ ρ * (2 * (ρ * η) + η ^ 2) := by
      rw [abs_mul]
      refine mul_le_mul ha ?_ (abs_nonneg _) hρ.le
      calc |2 * p - η ^ 2| ≤ |2 * p| + |η ^ 2| := abs_sub _ _
        _ = 2 * |p| + η ^ 2 := by
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (sq_nonneg η)]
        _ ≤ 2 * (ρ * η) + η ^ 2 := by linarith
    have hB : |b * ρ ^ 2| ≤ η * ρ ^ 2 := by
      rw [abs_mul, abs_of_pos hρ2]
      exact mul_le_mul_of_nonneg_right hb hρ2.le
    calc |a * (2 * p - η ^ 2) - b * ρ ^ 2| ≤ |a * (2 * p - η ^ 2)| + |b * ρ ^ 2| := abs_sub _ _
      _ ≤ ρ * (2 * (ρ * η) + η ^ 2) + η * ρ ^ 2 := add_le_add hA hB
      _ ≤ 4 * ρ ^ 2 * η := by nlinarith [mul_nonneg hρ.le hη]
  calc |a * (2 * p - η ^ 2) - b * ρ ^ 2| * ρ ^ 2 ≤ 4 * ρ ^ 2 * η * ρ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 hρ2.le
    _ ≤ 16 * η * (σ * ρ ^ 2) := by
        have : ρ ^ 2 ≤ 4 * σ := by linarith
        nlinarith [mul_nonneg hη hρ2.le, mul_nonneg (mul_nonneg hη hρ2.le) hρ2.le]

/-- The dot product of two planar sites is at most the product of their norms. -/
private lemma gamma_ball_sum_planar_abs_dot_le_mul (u v : Site 2) :
    |gamma_ball_sum_planar_dot u v| ≤ euclidNorm u * euclidNorm v := by
  rw [euclidNorm, euclidNorm, ← Real.sqrt_mul (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  apply Real.abs_le_sqrt
  simp only [gamma_ball_sum_planar_dot, Fin.sum_univ_two]
  nlinarith [sq_nonneg (((u 0 : ℤ) : ℝ) * ((v 1 : ℤ) : ℝ) - ((u 1 : ℤ) : ℝ) * ((v 0 : ℤ) : ℝ))]

/-- The dot product is additive in the second argument: `e · (x - y) = e · x - e · y`. -/
private lemma gamma_ball_sum_planar_dot_sub (e x y : Site 2) :
    gamma_ball_sum_planar_dot e (x - y) =
      gamma_ball_sum_planar_dot e x - gamma_ball_sum_planar_dot e y := by
  simp only [gamma_ball_sum_planar_dot, Fin.sum_univ_two, Pi.sub_apply, Int.cast_sub]
  ring

/-- The squared norm of a difference: `|x - y|² = |x|² - 2 x · y + |y|²`. -/
private lemma gamma_ball_sum_planar_norm_sub_sq (x y : Site 2) :
    euclidNorm (x - y) ^ 2 =
      euclidNorm x ^ 2 - 2 * gamma_ball_sum_planar_dot x y + euclidNorm y ^ 2 := by
  rw [gamma_ball_sum_planar_norm_sq, gamma_ball_sum_planar_norm_sq,
    gamma_ball_sum_planar_norm_sq]
  simp only [gamma_ball_sum_planar_dot, Fin.sum_univ_two, Pi.sub_apply, Int.cast_sub]
  ring

/-- Translating the base point by `y` changes `(e · w)/|w|²` by `O(|y|/|x|²)`, for `w = x - y`
and `|x| ≥ 2|y|`. -/
private lemma gamma_ball_sum_planar_translate {e : Site 2} (he : e ∈ unitSteps 2) (x y : Site 2)
    (hx : 2 * euclidNorm y ≤ euclidNorm x) (hx1 : 1 ≤ euclidNorm x) :
    |gamma_ball_sum_planar_dot e (x - y) / euclidNorm (x - y) ^ 2 -
        gamma_ball_sum_planar_dot e x / euclidNorm x ^ 2| ≤
      16 * euclidNorm y / euclidNorm x ^ 2 := by
  rw [gamma_ball_sum_planar_dot_sub]
  refine gamma_ball_sum_planar_translate_real (p := gamma_ball_sum_planar_dot x y)
    (by linarith) (euclidNorm_nonneg y) hx (gamma_ball_sum_planar_abs_dot_le he x) ?_ ?_
    (gamma_ball_sum_planar_norm_sub_sq x y)
  · have h := gamma_ball_sum_planar_abs_dot_le_mul e y
    rwa [euclidNorm_of_mem_unitSteps he, one_mul] at h
  · exact gamma_ball_sum_planar_abs_dot_le_mul x y

/-- For a fixed translate `y`, `b(x - y + e) - b(x - y) = (2/π)(e · x)/|x|² + O(|x|^{-2})`. -/
private theorem gamma_ball_sum_planar_translated_increment (y : Site 2) :
    ∃ K R : ℝ, 0 ≤ K ∧ 1 ≤ R ∧ ∀ (x e : Site 2), e ∈ unitSteps 2 → R ≤ euclidNorm x →
      |latticeKernel 2 (x - y + e) - latticeKernel 2 (x - y) -
        2 / Real.pi * (gamma_ball_sum_planar_dot e x / euclidNorm x ^ 2)| ≤
          K / euclidNorm x ^ 2 := by
  obtain ⟨K₁, R₁, hK₁, hR₁, hinc⟩ := gamma_ball_sum_planar_increment
  have hy := euclidNorm_nonneg y
  refine ⟨4 * K₁ + 32 / Real.pi * euclidNorm y, 2 * R₁ + 2 * euclidNorm y, by positivity,
    by linarith, ?_⟩
  intro x e he hx
  have hx1 : 1 ≤ euclidNorm x := by linarith
  have hxpos : 0 < euclidNorm x := by linarith
  have hw : euclidNorm x / 2 ≤ euclidNorm (x - y) := by
    have h := euclidNorm_add_le (x - y) y
    rw [sub_add_cancel] at h
    linarith
  have hwR : R₁ ≤ euclidNorm (x - y) := by linarith
  have h1 := hinc (x - y) e he hwR
  have h2 := gamma_ball_sum_planar_translate he x y (by linarith) hx1
  have hρ2 : 0 < euclidNorm x ^ 2 := by positivity
  have hinv : K₁ / euclidNorm (x - y) ^ 2 ≤ 4 * K₁ / euclidNorm x ^ 2 := by
    rw [div_le_div_iff₀ (by nlinarith) hρ2]
    have : euclidNorm x ^ 2 ≤ 4 * euclidNorm (x - y) ^ 2 := by nlinarith
    nlinarith
  have hpi : 0 < 2 / Real.pi := by positivity
  have hsplit : latticeKernel 2 (x - y + e) - latticeKernel 2 (x - y) -
        2 / Real.pi * (gamma_ball_sum_planar_dot e x / euclidNorm x ^ 2) =
      (latticeKernel 2 (x - y + e) - latticeKernel 2 (x - y) -
        2 / Real.pi * (gamma_ball_sum_planar_dot e (x - y) / euclidNorm (x - y) ^ 2)) +
        2 / Real.pi * (gamma_ball_sum_planar_dot e (x - y) / euclidNorm (x - y) ^ 2 -
          gamma_ball_sum_planar_dot e x / euclidNorm x ^ 2) := by ring
  rw [hsplit]
  calc |(latticeKernel 2 (x - y + e) - latticeKernel 2 (x - y) -
        2 / Real.pi * (gamma_ball_sum_planar_dot e (x - y) / euclidNorm (x - y) ^ 2)) +
        2 / Real.pi * (gamma_ball_sum_planar_dot e (x - y) / euclidNorm (x - y) ^ 2 -
          gamma_ball_sum_planar_dot e x / euclidNorm x ^ 2)|
      ≤ |latticeKernel 2 (x - y + e) - latticeKernel 2 (x - y) -
        2 / Real.pi * (gamma_ball_sum_planar_dot e (x - y) / euclidNorm (x - y) ^ 2)| +
        |2 / Real.pi * (gamma_ball_sum_planar_dot e (x - y) / euclidNorm (x - y) ^ 2 -
          gamma_ball_sum_planar_dot e x / euclidNorm x ^ 2)| := abs_add_le _ _
    _ ≤ 4 * K₁ / euclidNorm x ^ 2 + 2 / Real.pi * (16 * euclidNorm y / euclidNorm x ^ 2) := by
        refine add_le_add (h1.trans hinv) ?_
        rw [abs_mul, abs_of_pos hpi]
        exact mul_le_mul_of_nonneg_left h2 hpi.le
    _ = (4 * K₁ + 32 / Real.pi * euclidNorm y) / euclidNorm x ^ 2 := by
        field_simp
        ring

/-- The increments of `combo b y s` are `A (e · x)/|x|² + O(|x|^{-2})` with `A = (2/π) Σ s_i`. -/
private theorem gamma_ball_sum_planar_combo_increment {k : ℕ} (y : Fin k → Site 2)
    (s : Fin k → ℝ) :
    ∃ K R : ℝ, 0 ≤ K ∧ 1 ≤ R ∧ ∀ (x e : Site 2), e ∈ unitSteps 2 → R ≤ euclidNorm x →
      |combo (latticeKernel 2) y s (x + e) - combo (latticeKernel 2) y s x -
        2 / Real.pi * (∑ i, s i) * (gamma_ball_sum_planar_dot e x / euclidNorm x ^ 2)| ≤
          K / euclidNorm x ^ 2 := by
  choose K R hK hR h using fun i => gamma_ball_sum_planar_translated_increment (y i)
  refine ⟨∑ i, |s i| * K i, 1 + ∑ i, |R i|, Finset.sum_nonneg fun i _ =>
    mul_nonneg (abs_nonneg _) (hK i), ?_, ?_⟩
  · linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (R i))]
  · intro x e he hx
    have hRi : ∀ i, R i ≤ euclidNorm x := fun i => by
      have := Finset.single_le_sum (f := fun i => |R i|) (fun i _ => abs_nonneg (R i))
        (Finset.mem_univ i)
      linarith [le_abs_self (R i)]
    have hdecomp : combo (latticeKernel 2) y s (x + e) - combo (latticeKernel 2) y s x -
        2 / Real.pi * (∑ i, s i) * (gamma_ball_sum_planar_dot e x / euclidNorm x ^ 2) =
        ∑ i, s i * (latticeKernel 2 (x - y i + e) - latticeKernel 2 (x - y i) -
          2 / Real.pi * (gamma_ball_sum_planar_dot e x / euclidNorm x ^ 2)) := by
      simp only [combo, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, add_sub_right_comm]
      ring
    rw [hdecomp]
    calc |∑ i, s i * (latticeKernel 2 (x - y i + e) - latticeKernel 2 (x - y i) -
          2 / Real.pi * (gamma_ball_sum_planar_dot e x / euclidNorm x ^ 2))|
        ≤ ∑ i, |s i * (latticeKernel 2 (x - y i + e) - latticeKernel 2 (x - y i) -
          2 / Real.pi * (gamma_ball_sum_planar_dot e x / euclidNorm x ^ 2))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |s i| * (K i / euclidNorm x ^ 2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (h i x e he (hRi i)) (abs_nonneg _)
      _ = (∑ i, |s i| * K i) / euclidNorm x ^ 2 := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by ring

/-- The algebra of the four unit steps: with `F_e = A (e · x)/|x|² + E_e` the bracket is
`A²/(2|x|²)` up to `O(|x|^{-3})`, written with `r = 1/|x|` and `p_i = x_i/|x|²`. -/
private lemma gamma_ball_sum_planar_quad {A p0 p1 r E1 E2 E3 E4 K : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hK : 0 ≤ K) (hp0 : |p0| ≤ r) (hp1 : |p1| ≤ r) (hp : p0 ^ 2 + p1 ^ 2 = r ^ 2)
    (h1 : |E1| ≤ K * r ^ 2) (h2 : |E2| ≤ K * r ^ 2) (h3 : |E3| ≤ K * r ^ 2)
    (h4 : |E4| ≤ K * r ^ 2) :
    |(1 / 4) * ((A * p0 + E1) ^ 2 + (-(A * p0) + E2) ^ 2 + (A * p1 + E3) ^ 2 +
        (-(A * p1) + E4) ^ 2) -
      (((A * p0 + E1) + (-(A * p0) + E2) + (A * p1 + E3) + (-(A * p1) + E4)) / 4) ^ 2 -
      A ^ 2 * r ^ 2 / 2| ≤ (2 * |A| * K + K ^ 2) * r ^ 3 := by
  have hid : (1 / 4) * ((A * p0 + E1) ^ 2 + (-(A * p0) + E2) ^ 2 + (A * p1 + E3) ^ 2 +
        (-(A * p1) + E4) ^ 2) -
      (((A * p0 + E1) + (-(A * p0) + E2) + (A * p1 + E3) + (-(A * p1) + E4)) / 4) ^ 2 -
      A ^ 2 * r ^ 2 / 2 =
      (A / 2) * (p0 * (E1 - E2) + p1 * (E3 - E4)) +
        ((1 / 4) * (E1 ^ 2 + E2 ^ 2 + E3 ^ 2 + E4 ^ 2) - (E1 + E2 + E3 + E4) ^ 2 / 16) := by
    linear_combination (A ^ 2 / 2) * hp
  rw [hid]
  have hKr : 0 ≤ K * r ^ 2 := by positivity
  have hE : ∀ E : ℝ, |E| ≤ K * r ^ 2 → E ^ 2 ≤ (K * r ^ 2) ^ 2 := fun E hE => by
    rw [← sq_abs E]
    exact pow_le_pow_left₀ (abs_nonneg _) hE 2
  have hsum : |E1 + E2 + E3 + E4| ≤ 4 * (K * r ^ 2) := by
    calc |E1 + E2 + E3 + E4| ≤ |E1 + E2 + E3| + |E4| := abs_add_le _ _
      _ ≤ (|E1 + E2| + |E3|) + |E4| := by gcongr; exact abs_add_le _ _
      _ ≤ ((|E1| + |E2|) + |E3|) + |E4| := by gcongr; exact abs_add_le _ _
      _ ≤ 4 * (K * r ^ 2) := by linarith
  have hsum2 : (E1 + E2 + E3 + E4) ^ 2 ≤ (4 * (K * r ^ 2)) ^ 2 := by
    rw [← sq_abs (E1 + E2 + E3 + E4)]
    exact pow_le_pow_left₀ (abs_nonneg _) hsum 2
  have hquad : |(1 / 4) * (E1 ^ 2 + E2 ^ 2 + E3 ^ 2 + E4 ^ 2) - (E1 + E2 + E3 + E4) ^ 2 / 16| ≤
      K ^ 2 * r ^ 3 := by
    have hr4 : K ^ 2 * r ^ 4 ≤ K ^ 2 * r ^ 3 := by
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg K)
      calc r ^ 4 = r ^ 3 * r := by ring
        _ ≤ r ^ 3 * 1 := mul_le_mul_of_nonneg_left hr1 (by positivity)
        _ = r ^ 3 := mul_one _
    have hKr4 : (K * r ^ 2) ^ 2 = K ^ 2 * r ^ 4 := by ring
    have h16 : (4 * (K * r ^ 2)) ^ 2 = 16 * (K ^ 2 * r ^ 4) := by ring
    have hA : (1 / 4) * (E1 ^ 2 + E2 ^ 2 + E3 ^ 2 + E4 ^ 2) ≤ K ^ 2 * r ^ 4 := by
      linarith [hE E1 h1, hE E2 h2, hE E3 h3, hE E4 h4]
    have hB : (E1 + E2 + E3 + E4) ^ 2 / 16 ≤ K ^ 2 * r ^ 4 := by linarith
    have hX0 : 0 ≤ (1 / 4) * (E1 ^ 2 + E2 ^ 2 + E3 ^ 2 + E4 ^ 2) := by positivity
    have hY0 : 0 ≤ (E1 + E2 + E3 + E4) ^ 2 / 16 := by positivity
    rw [abs_le]
    constructor <;> linarith
  have hlin : |(A / 2) * (p0 * (E1 - E2) + p1 * (E3 - E4))| ≤ 2 * |A| * K * r ^ 3 := by
    rw [abs_mul, abs_div, abs_two]
    have hd1 : |p0 * (E1 - E2)| ≤ r * (2 * (K * r ^ 2)) := by
      rw [abs_mul]
      refine mul_le_mul hp0 ?_ (abs_nonneg _) hr0
      calc |E1 - E2| ≤ |E1| + |E2| := abs_sub _ _
        _ ≤ 2 * (K * r ^ 2) := by linarith
    have hd2 : |p1 * (E3 - E4)| ≤ r * (2 * (K * r ^ 2)) := by
      rw [abs_mul]
      refine mul_le_mul hp1 ?_ (abs_nonneg _) hr0
      calc |E3 - E4| ≤ |E3| + |E4| := abs_sub _ _
        _ ≤ 2 * (K * r ^ 2) := by linarith
    have hin : |p0 * (E1 - E2) + p1 * (E3 - E4)| ≤ 4 * K * r ^ 3 := by
      calc |p0 * (E1 - E2) + p1 * (E3 - E4)| ≤ |p0 * (E1 - E2)| + |p1 * (E3 - E4)| :=
            abs_add_le _ _
        _ ≤ r * (2 * (K * r ^ 2)) + r * (2 * (K * r ^ 2)) := add_le_add hd1 hd2
        _ = 4 * K * r ^ 3 := by ring
    calc |A| / 2 * |p0 * (E1 - E2) + p1 * (E3 - E4)| ≤ |A| / 2 * (4 * K * r ^ 3) :=
          mul_le_mul_of_nonneg_left hin (by positivity)
      _ = 2 * |A| * K * r ^ 3 := by ring
  calc |(A / 2) * (p0 * (E1 - E2) + p1 * (E3 - E4)) +
        ((1 / 4) * (E1 ^ 2 + E2 ^ 2 + E3 ^ 2 + E4 ^ 2) - (E1 + E2 + E3 + E4) ^ 2 / 16)|
      ≤ |(A / 2) * (p0 * (E1 - E2) + p1 * (E3 - E4))| +
        |(1 / 4) * (E1 ^ 2 + E2 ^ 2 + E3 ^ 2 + E4 ^ 2) - (E1 + E2 + E3 + E4) ^ 2 / 16| :=
        abs_add_le _ _
    _ ≤ 2 * |A| * K * r ^ 3 + K ^ 2 * r ^ 3 := add_le_add hlin hquad
    _ = (2 * |A| * K + K ^ 2) * r ^ 3 := by ring

/-- The bracket of a planar function in terms of its four unit increments. -/
private lemma gamma_ball_sum_planar_gammaBr_eq (f : Site 2 → ℝ) (x : Site 2) :
    gammaBr f f x = (1 / 4) * ((f (x + unit 0) - f x) ^ 2 + (f (x + -unit 0) - f x) ^ 2 +
      (f (x + unit 1) - f x) ^ 2 + (f (x + -unit 1) - f x) ^ 2) -
      (((f (x + unit 0) - f x) + (f (x + -unit 0) - f x) + (f (x + unit 1) - f x) +
        (f (x + -unit 1) - f x)) / 4) ^ 2 := by
  unfold gammaBr
  rw [sum_unitSteps]
  simp only [Fin.sum_univ_two, walkOp, nbrSum, sub_eq_add_neg]
  push_cast
  ring

/-- The dot product of `unit i` with `x` is the coordinate `x_i`. -/
private lemma gamma_ball_sum_planar_dot_unit (i : Fin 2) (x : Site 2) :
    gamma_ball_sum_planar_dot (unit i) x = ((x i : ℤ) : ℝ) := by
  fin_cases i <;> simp [gamma_ball_sum_planar_dot, Fin.sum_univ_two, unit]

/-- The dot product of `-unit i` with `x` is `-x_i`. -/
private lemma gamma_ball_sum_planar_dot_neg_unit (i : Fin 2) (x : Site 2) :
    gamma_ball_sum_planar_dot (-unit i) x = -((x i : ℤ) : ℝ) := by
  fin_cases i <;> simp [gamma_ball_sum_planar_dot, Fin.sum_univ_two, unit]

/-- The asymptotics of the planar bracket: `Γ(x) = 2 (Σ s)²/(π² |x|²) + O(|x|^{-3})`. -/
private theorem gamma_ball_sum_planar_gamma_asymp {k : ℕ} (y : Fin k → Site 2)
    (s : Fin k → ℝ) :
    ∃ K R : ℝ, 0 ≤ K ∧ 1 ≤ R ∧ ∀ x : Site 2, R ≤ euclidNorm x →
      |gammaBr (combo (latticeKernel 2) y s) (combo (latticeKernel 2) y s) x -
        2 * (∑ i, s i) ^ 2 / Real.pi ^ 2 / euclidNorm x ^ 2| ≤ K / euclidNorm x ^ 3 := by
  obtain ⟨K₀, R₀, hK₀, hR₀, hinc⟩ := gamma_ball_sum_planar_combo_increment y s
  set f := combo (latticeKernel 2) y s with hf
  set A : ℝ := 2 / Real.pi * ∑ i, s i with hA
  refine ⟨(2 * |A| * K₀ + K₀ ^ 2), R₀, by positivity, hR₀, ?_⟩
  intro x hx
  set ρ := euclidNorm x with hρ
  have hρ1 : 1 ≤ ρ := hR₀.trans hx
  have hρpos : 0 < ρ := by linarith
  have hρ2 : 0 < ρ ^ 2 := by positivity
  set r : ℝ := 1 / ρ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one hρpos]
    exact hρ1
  have hr2 : r ^ 2 = 1 / ρ ^ 2 := by rw [hr, div_pow, one_pow]
  have hr3 : r ^ 3 = 1 / ρ ^ 3 := by rw [hr, div_pow, one_pow]
  set p0 : ℝ := ((x 0 : ℤ) : ℝ) / ρ ^ 2 with hp0def
  set p1 : ℝ := ((x 1 : ℤ) : ℝ) / ρ ^ 2 with hp1def
  have hcoord : ∀ i : Fin 2, |((x i : ℤ) : ℝ)| / ρ ^ 2 ≤ r := fun i => by
    rw [hr, div_le_div_iff₀ hρ2 hρpos]
    have := CERW.Support.Law.abs_coord_le_euclidNorm x i
    nlinarith
  have hp0 : |p0| ≤ r := by
    rw [hp0def, abs_div, abs_of_pos hρ2]
    exact hcoord 0
  have hp1 : |p1| ≤ r := by
    rw [hp1def, abs_div, abs_of_pos hρ2]
    exact hcoord 1
  have hp : p0 ^ 2 + p1 ^ 2 = r ^ 2 := by
    have hn : ρ ^ 2 = ((x 0 : ℤ) : ℝ) ^ 2 + ((x 1 : ℤ) : ℝ) ^ 2 :=
      gamma_ball_sum_planar_norm_sq x
    rw [hp0def, hp1def, hr2, div_pow, div_pow]
    rw [← add_div, ← hn]
    field_simp
  have hE : ∀ e ∈ unitSteps 2,
      |f (x + e) - f x - A * (gamma_ball_sum_planar_dot e x / ρ ^ 2)| ≤ K₀ * r ^ 2 := by
    intro e he
    have h := hinc x e he hx
    rw [hr2, ← div_eq_mul_one_div]
    exact h
  have hu0 : unit 0 ∈ unitSteps 2 := mem_unitSteps.mpr ⟨0, Or.inl rfl⟩
  have hu0' : -unit 0 ∈ unitSteps 2 := mem_unitSteps.mpr ⟨0, Or.inr rfl⟩
  have hu1 : unit 1 ∈ unitSteps 2 := mem_unitSteps.mpr ⟨1, Or.inl rfl⟩
  have hu1' : -unit 1 ∈ unitSteps 2 := mem_unitSteps.mpr ⟨1, Or.inr rfl⟩
  have hE1 := hE _ hu0
  have hE2 := hE _ hu0'
  have hE3 := hE _ hu1
  have hE4 := hE _ hu1'
  rw [gamma_ball_sum_planar_dot_unit, ← hp0def] at hE1
  rw [gamma_ball_sum_planar_dot_neg_unit, neg_div, ← hp0def, mul_neg, sub_neg_eq_add] at hE2
  rw [gamma_ball_sum_planar_dot_unit, ← hp1def] at hE3
  rw [gamma_ball_sum_planar_dot_neg_unit, neg_div, ← hp1def, mul_neg, sub_neg_eq_add] at hE4
  have hq := gamma_ball_sum_planar_quad (A := A) hr0 hr1 hK₀ hp0 hp1 hp hE1 hE2 hE3 hE4
  have hkey : gammaBr f f x - A ^ 2 * r ^ 2 / 2 =
      (1 / 4) * ((A * p0 + (f (x + unit 0) - f x - A * p0)) ^ 2 +
        (-(A * p0) + (f (x + -unit 0) - f x + A * p0)) ^ 2 +
        (A * p1 + (f (x + unit 1) - f x - A * p1)) ^ 2 +
        (-(A * p1) + (f (x + -unit 1) - f x + A * p1)) ^ 2) -
      (((A * p0 + (f (x + unit 0) - f x - A * p0)) +
        (-(A * p0) + (f (x + -unit 0) - f x + A * p0)) +
        (A * p1 + (f (x + unit 1) - f x - A * p1)) +
        (-(A * p1) + (f (x + -unit 1) - f x + A * p1))) / 4) ^ 2 -
      A ^ 2 * r ^ 2 / 2 := by
    rw [gamma_ball_sum_planar_gammaBr_eq]
    ring
  have hmain : A ^ 2 * r ^ 2 / 2 = 2 * (∑ i, s i) ^ 2 / Real.pi ^ 2 / ρ ^ 2 := by
    rw [hA, hr2]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [← hmain]
  have hcalc : |gammaBr f f x - A ^ 2 * r ^ 2 / 2| ≤ (2 * |A| * K₀ + K₀ ^ 2) * r ^ 3 := by
    rw [hkey]
    exact hq
  rwa [hr3, mul_one_div] at hcalc

/-- The weight `(1 + |x|)^{-3}` is summable over the planar lattice. -/
private lemma gamma_ball_sum_planar_summable_cube :
    Summable (fun x : Site 2 => ((1 + euclidNorm x) ^ 3)⁻¹) := by
  have h := summable_one_add_euclidNorm_rpow 2 (p := 3) (by norm_num)
  refine h.congr fun x => ?_
  rw [Real.rpow_neg (by linarith [euclidNorm_nonneg x]),
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The bracket minus its leading term `c₀ |x|^{-2}` (cut off below `|x| = 1`) is
`O((1 + |x|)^{-3})` on the whole lattice. -/
private lemma gamma_ball_sum_planar_remainder_bound {k : ℕ} (y : Fin k → Site 2)
    (s : Fin k → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Site 2,
      |gammaBr (combo (latticeKernel 2) y s) (combo (latticeKernel 2) y s) x -
        (if 1 ≤ euclidNorm x then 2 * (∑ i, s i) ^ 2 / Real.pi ^ 2 * (euclidNorm x ^ 2)⁻¹
          else 0)| ≤ K * ((1 + euclidNorm x) ^ 3)⁻¹ := by
  obtain ⟨K₃, R₀, hK₃, hR₀, hasymp⟩ := gamma_ball_sum_planar_gamma_asymp y s
  set Γ := gammaBr (combo (latticeKernel 2) y s) (combo (latticeKernel 2) y s) with hΓ
  set c₀ : ℝ := 2 * (∑ i, s i) ^ 2 / Real.pi ^ 2 with hc₀
  set M : ℝ := ∑ z ∈ ballFinset 2 R₀, |Γ z| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun z _ => abs_nonneg _
  refine ⟨max (8 * K₃) ((M + |c₀|) * (1 + R₀) ^ 3), le_max_of_le_left (by positivity), ?_⟩
  intro x
  have hρ0 : 0 ≤ euclidNorm x := euclidNorm_nonneg x
  by_cases hx : R₀ ≤ euclidNorm x
  · have hρ1 : 1 ≤ euclidNorm x := hR₀.trans hx
    have hρpos : 0 < euclidNorm x := by linarith
    rw [if_pos hρ1, ← div_eq_mul_inv]
    calc |Γ x - c₀ / euclidNorm x ^ 2| ≤ K₃ / euclidNorm x ^ 3 := hasymp x hx
      _ ≤ 8 * K₃ * ((1 + euclidNorm x) ^ 3)⁻¹ := by
          rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
          have h8 : (1 + euclidNorm x) ^ 3 ≤ 8 * euclidNorm x ^ 3 := by
            calc (1 + euclidNorm x) ^ 3 ≤ (2 * euclidNorm x) ^ 3 :=
                  pow_le_pow_left₀ (by linarith) (by linarith) 3
              _ = 8 * euclidNorm x ^ 3 := by ring
          exact (mul_le_mul_of_nonneg_left h8 hK₃).trans_eq (by ring)
      _ ≤ max (8 * K₃) ((M + |c₀|) * (1 + R₀) ^ 3) * ((1 + euclidNorm x) ^ 3)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hxR : euclidNorm x ≤ R₀ := (not_le.mp hx).le
    have hΓx : |Γ x| ≤ M :=
      Finset.single_le_sum (f := fun z => |Γ z|) (fun z _ => abs_nonneg _)
        (mem_ballFinset_iff.mpr hxR)
    have hg : |(if 1 ≤ euclidNorm x then c₀ * (euclidNorm x ^ 2)⁻¹ else 0)| ≤ |c₀| := by
      split_ifs with h1
      · rw [abs_mul, abs_of_nonneg (a := (euclidNorm x ^ 2)⁻¹) (inv_nonneg.mpr (sq_nonneg _))]
        have : (euclidNorm x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h1)
        calc |c₀| * (euclidNorm x ^ 2)⁻¹ ≤ |c₀| * 1 :=
              mul_le_mul_of_nonneg_left this (abs_nonneg _)
          _ = |c₀| := mul_one _
      · simp
    have hle : |Γ x - (if 1 ≤ euclidNorm x then c₀ * (euclidNorm x ^ 2)⁻¹ else 0)| ≤
        M + |c₀| := (abs_sub _ _).trans (add_le_add hΓx hg)
    refine hle.trans ?_
    have hpos1 : 0 < (1 + euclidNorm x) ^ 3 := by positivity
    have hmono : ((1 + R₀) ^ 3)⁻¹ ≤ ((1 + euclidNorm x) ^ 3)⁻¹ :=
      inv_anti₀ hpos1 (pow_le_pow_left₀ (by linarith) (by linarith) 3)
    have hpos2 : 0 < (1 + R₀) ^ 3 := by positivity
    calc M + |c₀| = (M + |c₀|) * (1 + R₀) ^ 3 * ((1 + R₀) ^ 3)⁻¹ := by
          field_simp
      _ ≤ (M + |c₀|) * (1 + R₀) ^ 3 * ((1 + euclidNorm x) ^ 3)⁻¹ :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ ≤ max (8 * K₃) ((M + |c₀|) * (1 + R₀) ^ 3) * ((1 + euclidNorm x) ^ 3)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- The planar weighted ball sum of `Γ`. -/
private theorem gamma_ball_sum_planar {k : ℕ} (y : Fin k → Site 2) (s : Fin k → ℝ) :
    ∃ C : ℝ, ∀ r : ℝ, 2 ≤ r →
      |∑ x ∈ ballFinset 2 r, (r - euclidNorm x) *
          gammaBr (combo (latticeKernel 2) y s) (combo (latticeKernel 2) y s) x
        - 4 / Real.pi * (∑ i, s i) ^ 2 * r * Real.log r| ≤ C * r := by
  obtain ⟨K₅, hK₅, hrem⟩ := gamma_ball_sum_planar_remainder_bound y s
  obtain ⟨C₁, hlog⟩ := CERW.Generic.Lattice.abs_sum_inv_sq_sub_log_le
  obtain ⟨Cp, hCp, hpack⟩ :=
    CERW.Generic.Lattice.sum_ballFinset_rpow_one_sub_le (d := 2) (by norm_num)
  have hC₁ : 0 ≤ C₁ := (abs_nonneg _).trans (hlog 1 le_rfl)
  set Γ := gammaBr (combo (latticeKernel 2) y s) (combo (latticeKernel 2) y s) with hΓ
  set c₀ : ℝ := 2 * (∑ i, s i) ^ 2 / Real.pi ^ 2 with hc₀
  set S : ℝ := ∑' x : Site 2, ((1 + euclidNorm x) ^ 3)⁻¹ with hS
  have hw0 : ∀ x : Site 2, 0 ≤ ((1 + euclidNorm x) ^ 3)⁻¹ := fun x =>
    inv_nonneg.mpr (pow_nonneg (by linarith [euclidNorm_nonneg x]) 3)
  have hS0 : 0 ≤ S := tsum_nonneg hw0
  refine ⟨K₅ * S + |c₀| * C₁ + 4 * |c₀| * Cp, ?_⟩
  intro r hr
  have hr0 : 0 ≤ r := by linarith
  set B := ballFinset 2 r with hB
  set F := B.filter (fun x => 1 ≤ euclidNorm x) with hF
  set g : Site 2 → ℝ := fun x =>
    if 1 ≤ euclidNorm x then c₀ * (euclidNorm x ^ 2)⁻¹ else 0 with hg
  have hmemB : ∀ x ∈ B, 0 ≤ r - euclidNorm x ∧ r - euclidNorm x ≤ r := fun x hx =>
    ⟨by linarith [mem_ballFinset_iff.mp hx], by linarith [euclidNorm_nonneg x]⟩
  have hsplit : ∑ x ∈ B, (r - euclidNorm x) * Γ x =
      ∑ x ∈ B, (r - euclidNorm x) * (Γ x - g x) + ∑ x ∈ B, (r - euclidNorm x) * g x := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  -- the remainder
  have hD : |∑ x ∈ B, (r - euclidNorm x) * (Γ x - g x)| ≤ K₅ * S * r := by
    calc |∑ x ∈ B, (r - euclidNorm x) * (Γ x - g x)|
        ≤ ∑ x ∈ B, |(r - euclidNorm x) * (Γ x - g x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ B, r * (K₅ * ((1 + euclidNorm x) ^ 3)⁻¹) := by
          refine Finset.sum_le_sum fun x hx => ?_
          rw [abs_mul, abs_of_nonneg (hmemB x hx).1]
          exact mul_le_mul (hmemB x hx).2 (hrem x) (abs_nonneg _) hr0
      _ = r * K₅ * ∑ x ∈ B, ((1 + euclidNorm x) ^ 3)⁻¹ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ ≤ r * K₅ * S := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hr0 hK₅)
          exact gamma_ball_sum_planar_summable_cube.sum_le_tsum B fun x _ => hw0 x
      _ = K₅ * S * r := by ring
  -- the main term
  have hG : ∑ x ∈ B, (r - euclidNorm x) * g x =
      c₀ * r * ∑ x ∈ F, (euclidNorm x ^ 2)⁻¹ -
        c₀ * ∑ x ∈ F, euclidNorm x * (euclidNorm x ^ 2)⁻¹ := by
    rw [hF, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hg]
    split_ifs
    · ring
    · ring
  have he2 : 0 ≤ ∑ x ∈ F, euclidNorm x * (euclidNorm x ^ 2)⁻¹ ∧
      ∑ x ∈ F, euclidNorm x * (euclidNorm x ^ 2)⁻¹ ≤ 2 * (Cp * (r + 1)) := by
    refine ⟨Finset.sum_nonneg fun x _ =>
      mul_nonneg (euclidNorm_nonneg x) (inv_nonneg.mpr (sq_nonneg _)), ?_⟩
    calc ∑ x ∈ F, euclidNorm x * (euclidNorm x ^ 2)⁻¹
        ≤ ∑ x ∈ F, 2 * (1 + euclidNorm x) ^ (1 - ((2 : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun x hx => ?_
          have h1 : 1 ≤ euclidNorm x := (Finset.mem_filter.mp hx).2
          have hρpos : 0 < euclidNorm x := by linarith
          rw [show (1 : ℝ) - ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
          have hcancel : euclidNorm x * (euclidNorm x ^ 2)⁻¹ = (euclidNorm x)⁻¹ := by
            field_simp
          rw [hcancel]
          calc (euclidNorm x)⁻¹ = 2 * (2 * euclidNorm x)⁻¹ := by field_simp
            _ ≤ 2 * (1 + euclidNorm x)⁻¹ :=
                mul_le_mul_of_nonneg_left (inv_anti₀ (by linarith) (by linarith)) (by norm_num)
      _ ≤ ∑ x ∈ B, 2 * (1 + euclidNorm x) ^ (1 - ((2 : ℕ) : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x _ _ =>
            mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith [euclidNorm_nonneg x]) _)
      _ = 2 * ∑ x ∈ B, (1 + euclidNorm x) ^ (1 - ((2 : ℕ) : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ 2 * (Cp * (r + 1)) := mul_le_mul_of_nonneg_left (hpack r hr0) (by norm_num)
  have hlogr := hlog r (by linarith)
  have hconst : 4 / Real.pi * (∑ i, s i) ^ 2 = c₀ * (2 * Real.pi) := by
    rw [hc₀]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  have hfinal : ∑ x ∈ B, (r - euclidNorm x) * Γ x - 4 / Real.pi * (∑ i, s i) ^ 2 * r *
        Real.log r =
      ∑ x ∈ B, (r - euclidNorm x) * (Γ x - g x) +
        (c₀ * r * (∑ x ∈ F, (euclidNorm x ^ 2)⁻¹ - 2 * Real.pi * Real.log r) -
          c₀ * ∑ x ∈ F, euclidNorm x * (euclidNorm x ^ 2)⁻¹) := by
    rw [hsplit, hG, hconst]
    ring
  rw [hfinal]
  have hA : |c₀ * r * (∑ x ∈ F, (euclidNorm x ^ 2)⁻¹ - 2 * Real.pi * Real.log r)| ≤
      |c₀| * C₁ * r := by
    rw [abs_mul, abs_mul, abs_of_nonneg hr0]
    calc |c₀| * r * |∑ x ∈ F, (euclidNorm x ^ 2)⁻¹ - 2 * Real.pi * Real.log r|
        ≤ |c₀| * r * C₁ := mul_le_mul_of_nonneg_left hlogr (by positivity)
      _ = |c₀| * C₁ * r := by ring
  have hE : |c₀ * ∑ x ∈ F, euclidNorm x * (euclidNorm x ^ 2)⁻¹| ≤ 4 * |c₀| * Cp * r := by
    rw [abs_mul, abs_of_nonneg he2.1]
    calc |c₀| * ∑ x ∈ F, euclidNorm x * (euclidNorm x ^ 2)⁻¹
        ≤ |c₀| * (2 * (Cp * (r + 1))) := mul_le_mul_of_nonneg_left he2.2 (abs_nonneg _)
      _ ≤ |c₀| * (4 * Cp * r) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          nlinarith
      _ = 4 * |c₀| * Cp * r := by ring
  calc |∑ x ∈ B, (r - euclidNorm x) * (Γ x - g x) +
        (c₀ * r * (∑ x ∈ F, (euclidNorm x ^ 2)⁻¹ - 2 * Real.pi * Real.log r) -
          c₀ * ∑ x ∈ F, euclidNorm x * (euclidNorm x ^ 2)⁻¹)|
      ≤ |∑ x ∈ B, (r - euclidNorm x) * (Γ x - g x)| +
        |c₀ * r * (∑ x ∈ F, (euclidNorm x ^ 2)⁻¹ - 2 * Real.pi * Real.log r) -
          c₀ * ∑ x ∈ F, euclidNorm x * (euclidNorm x ^ 2)⁻¹| := abs_add_le _ _
    _ ≤ K₅ * S * r + (|c₀ * r * (∑ x ∈ F, (euclidNorm x ^ 2)⁻¹ - 2 * Real.pi * Real.log r)| +
        |c₀ * ∑ x ∈ F, euclidNorm x * (euclidNorm x ^ 2)⁻¹|) :=
        add_le_add hD (abs_sub _ _)
    _ ≤ K₅ * S * r + (|c₀| * C₁ * r + 4 * |c₀| * Cp * r) := by gcongr
    _ = (K₅ * S + |c₀| * C₁ + 4 * |c₀| * Cp) * r := by ring

/-! ### Local times against a weight -/

/-- A real sequence within `η M + u_n` of `L` for every `η > 0`, with `u_n → 0`, tends to `L`. -/
private lemma tendsto_ell_sum_of_le {a u : ℕ → ℝ} {L M : ℝ} (hM : 0 ≤ M)
    (hu : Tendsto u atTop (𝓝 0))
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, |a n - L| ≤ η * M + u n) :
    Tendsto a atTop (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hM1 : 0 < M + 1 := by linarith
  have hη : 0 < δ / (2 * (M + 1)) := by positivity
  have hu' : ∀ᶠ n in atTop, u n < δ / 2 := by
    have := (Metric.tendsto_nhds.mp hu) (δ / 2) (by linarith)
    filter_upwards [this] with n hn
    rw [Real.dist_eq, sub_zero] at hn
    exact (le_abs_self _).trans_lt hn
  filter_upwards [h _ hη, hu'] with n h1 h2
  rw [Real.dist_eq]
  have h3 : δ / (2 * (M + 1)) * M ≤ δ / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- The local time vanishes off the departure range, so a sum over the departure range is a sum
over any finite set containing it. -/
private lemma tendsto_ell_sum_sum_eq_of_subset (Y : ℕ → Site d) (n : ℕ) {s : Finset (Site d)}
    (hs : departureRange Y n ⊆ s) (Γ : Site d → ℝ) :
    ∑ x ∈ departureRange Y n, (localTime Y n x : ℝ) * Γ x =
      ∑ x ∈ s, (localTime Y n x : ℝ) * Γ x := by
  refine Finset.sum_subset hs fun x _ hx => ?_
  have h0 : localTime Y n x = 0 := by
    rw [mem_departureRange_iff, not_lt, Nat.le_zero] at hx
    exact hx
  rw [h0]
  simp

/-- The pointwise limit `ℓ_n(x)/r_n → 2dε` at a fixed site. -/
private lemma tendsto_ell_sum_pointwise {ε : ℝ} (Y : ℕ → Site d) (r : ℕ → ℝ)
    (hr : Tendsto r atTop atTop)
    (hshape : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x : Site d,
      |(localTime Y n x : ℝ) - 2 * d * ε * max (r n - euclidNorm x) 0| ≤ η * r n)
    (x : Site d) :
    Tendsto (fun n => (localTime Y n x : ℝ) / r n) atTop (𝓝 (2 * d * ε)) := by
  have hu : Tendsto (fun n => 2 * |(d : ℝ) * ε| * euclidNorm x / r n) atTop (𝓝 0) :=
    hr.const_div_atTop _
  refine tendsto_ell_sum_of_le (M := 1) zero_le_one hu fun η hη => ?_
  filter_upwards [hshape η hη, hr.eventually_gt_atTop (euclidNorm x), hr.eventually_gt_atTop 0]
    with n h1 h2 h3
  have h4 := h1 x
  rw [max_eq_left (by linarith)] at h4
  have hdiv : (localTime Y n x : ℝ) / r n - 2 * d * ε =
      ((localTime Y n x : ℝ) - 2 * d * ε * (r n - euclidNorm x)) / r n -
        2 * d * ε * euclidNorm x / r n := by
    field_simp
    ring
  rw [hdiv]
  have h5 : |((localTime Y n x : ℝ) - 2 * d * ε * (r n - euclidNorm x)) / r n| ≤ η := by
    rw [abs_div, abs_of_pos h3, div_le_iff₀ h3]
    exact h4
  have h6 : |2 * d * ε * euclidNorm x / r n| ≤ 2 * |(d : ℝ) * ε| * euclidNorm x / r n := by
    rw [abs_div, abs_of_pos h3]
    refine div_le_div_of_nonneg_right ?_ h3.le
    rw [abs_mul, abs_mul, abs_of_nonneg (euclidNorm_nonneg x)]
    simp only [abs_mul, abs_two, Nat.abs_cast]
    nlinarith [abs_nonneg ε, euclidNorm_nonneg x]
  calc |((localTime Y n x : ℝ) - 2 * d * ε * (r n - euclidNorm x)) / r n -
        2 * d * ε * euclidNorm x / r n|
      ≤ |((localTime Y n x : ℝ) - 2 * d * ε * (r n - euclidNorm x)) / r n| +
        |2 * d * ε * euclidNorm x / r n| := abs_sub _ _
    _ ≤ η * 1 + 2 * |(d : ℝ) * ε| * euclidNorm x / r n := by linarith

/-- `d ≥ 3`: `ℓ_n(x)/r_n → 2dε` with domination. -/
private theorem tendsto_ell_sum_high {ε : ℝ} (Y : ℕ → Site d) (r : ℕ → ℝ)
    (hr : Tendsto r atTop atTop)
    (hshape : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x : Site d,
      |(localTime Y n x : ℝ) - 2 * d * ε * max (r n - euclidNorm x) 0| ≤ η * r n)
    (Γ : Site d → ℝ) (hΓ : Summable Γ) :
    Tendsto (fun n => (∑ x ∈ departureRange Y n, (localTime Y n x : ℝ) * Γ x) / r n) atTop
      (𝓝 (2 * d * ε * ∑' x, Γ x)) := by
  have hT : Tendsto (fun n => ∑' x, (localTime Y n x : ℝ) / r n * Γ x) atTop
      (𝓝 (∑' x, 2 * d * ε * Γ x)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun x => (2 * d * |ε| + 1) * |Γ x|)
      (hΓ.abs.mul_left _) (fun x => (tendsto_ell_sum_pointwise Y r hr hshape x).mul_const _) ?_
    filter_upwards [hshape 1 one_pos, hr.eventually_gt_atTop 0] with n h1 h2 x
    have h3 := h1 x
    have h4 : (localTime Y n x : ℝ) ≤ (2 * d * |ε| + 1) * r n := by
      have h5 : max (r n - euclidNorm x) 0 ≤ r n :=
        max_le (by linarith [euclidNorm_nonneg x]) h2.le
      have h6 : 2 * (d : ℝ) * ε * max (r n - euclidNorm x) 0 ≤ 2 * d * |ε| * r n := by
        have hM : 0 ≤ max (r n - euclidNorm x) 0 := le_max_right _ _
        calc 2 * (d : ℝ) * ε * max (r n - euclidNorm x) 0
            ≤ 2 * d * |ε| * max (r n - euclidNorm x) 0 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (le_abs_self ε) (by positivity)) hM
          _ ≤ 2 * d * |ε| * r n := mul_le_mul_of_nonneg_left h5 (by positivity)
      linarith [(abs_le.mp h3).2]
    have h7 : 0 ≤ (localTime Y n x : ℝ) := Nat.cast_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg h7 h2.le)]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [div_le_iff₀ h2]
    exact h4
  rw [tsum_mul_left] at hT
  refine hT.congr' ?_
  filter_upwards [hr.eventually_gt_atTop 0] with n hn
  rw [tsum_eq_sum (s := departureRange Y n), Finset.sum_div]
  · exact Finset.sum_congr rfl fun x _ => by ring
  · intro x hx
    have h0 : localTime Y n x = 0 := by
      rw [mem_departureRange_iff, not_lt, Nat.le_zero] at hx
      exact hx
    simp [h0]

/-- The planar profile sum over `|x| ≤ 2R` equals the sum over `|x| ≤ R` of `(R - |x|) Γ`. -/
private lemma tendsto_ell_sum_planar_profile (R : ℝ) (hR : 0 ≤ R) (Γ : Site 2 → ℝ) :
    ∑ x ∈ ballFinset 2 (2 * R), max (R - euclidNorm x) 0 * Γ x =
      ∑ x ∈ ballFinset 2 R, (R - euclidNorm x) * Γ x := by
  symm
  have hsub : ballFinset 2 R ⊆ ballFinset 2 (2 * R) := by
    intro x hx
    rw [mem_ballFinset_iff] at hx ⊢
    linarith
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [mem_ballFinset_iff] at hx
    rw [max_eq_left (by linarith)]
  · intro x _ hx
    rw [mem_ballFinset_iff, not_le] at hx
    rw [max_eq_right (by linarith)]
    simp

/-- One time step of the planar comparison: the local time sum is within
`η R C₁ Σ_{|x| ≤ 2R} (1 + |x|)^{-2}` of `4ε Σ_{|x| ≤ R} (R - |x|) Γ(x)`. -/
private lemma tendsto_ell_sum_planar_step {ε : ℝ} (Y : ℕ → Site 2) (n : ℕ) (R η : ℝ)
    (hR : 0 ≤ R) (hA : ∀ x ∈ departureRange Y n, euclidNorm x ≤ 2 * R)
    (hshape : ∀ x : Site 2,
      |(localTime Y n x : ℝ) - 4 * ε * max (R - euclidNorm x) 0| ≤ η * R)
    (Γ : Site 2 → ℝ) (C₁ : ℝ) (hΓ : ∀ x, |Γ x| ≤ C₁ * (1 + euclidNorm x) ^ (-2 : ℝ)) :
    |∑ x ∈ departureRange Y n, (localTime Y n x : ℝ) * Γ x -
        4 * ε * ∑ x ∈ ballFinset 2 R, (R - euclidNorm x) * Γ x| ≤
      η * R * (C₁ * ∑ x ∈ ballFinset 2 (2 * R), (1 + euclidNorm x) ^ (-2 : ℝ)) := by
  have hball : departureRange Y n ⊆ ballFinset 2 (2 * R) := fun x hx =>
    mem_ballFinset_iff.mpr (hA x hx)
  rw [tendsto_ell_sum_sum_eq_of_subset Y n hball, ← tendsto_ell_sum_planar_profile R hR,
    Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  have h1 : (localTime Y n x : ℝ) * Γ x - 4 * ε * (max (R - euclidNorm x) 0 * Γ x) =
      ((localTime Y n x : ℝ) - 4 * ε * max (R - euclidNorm x) 0) * Γ x := by ring
  rw [h1, abs_mul]
  calc |(localTime Y n x : ℝ) - 4 * ε * max (R - euclidNorm x) 0| * |Γ x|
      ≤ (η * R) * (C₁ * (1 + euclidNorm x) ^ (-2 : ℝ)) :=
        mul_le_mul (hshape x) (hΓ x) (abs_nonneg _) ((abs_nonneg _).trans (hshape x))
    _ = η * R * (C₁ * (1 + euclidNorm x) ^ (-2 : ℝ)) := rfl

/-- `d = 2`. -/
private theorem tendsto_ell_sum_planar {ε : ℝ} (Y : ℕ → Site 2) (r : ℕ → ℝ)
    (hr : Tendsto r atTop atTop)
    (hA : ∀ᶠ n in atTop, ∀ x ∈ departureRange Y n, euclidNorm x ≤ 2 * r n)
    (hshape : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x : Site 2,
      |(localTime Y n x : ℝ) - 4 * ε * max (r n - euclidNorm x) 0| ≤ η * r n)
    (Γ : Site 2 → ℝ) (C₁ : ℝ) (hΓ : ∀ x, |Γ x| ≤ C₁ * (1 + euclidNorm x) ^ (-2 : ℝ))
    (c : ℝ) (hT : ∃ C : ℝ, ∀ ρ : ℝ, 2 ≤ ρ →
      |∑ x ∈ ballFinset 2 ρ, (ρ - euclidNorm x) * Γ x - c * ρ * Real.log ρ| ≤ C * ρ) :
    Tendsto (fun n => (∑ x ∈ departureRange Y n, (localTime Y n x : ℝ) * Γ x) /
      (r n * Real.log (r n))) atTop (𝓝 (4 * ε * c)) := by
  obtain ⟨CT, hCT⟩ := hT
  obtain ⟨CL, hCLpos, hCL⟩ := CERW.Generic.Lattice.sum_ballFinset_rpow_neg_le_log (d := 2)
    (by norm_num)
  set C1 : ℝ := max C₁ 0 with hC1
  have hC1nn : 0 ≤ C1 := le_max_right _ _
  have hΓ' : ∀ x, |Γ x| ≤ C1 * (1 + euclidNorm x) ^ (-2 : ℝ) := fun x =>
    (hΓ x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by linarith [euclidNorm_nonneg x]) _))
  have hlog : Tendsto (fun n => Real.log (r n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hr
  have hu : Tendsto (fun n => 4 * |ε| * CT / Real.log (r n)) atTop (𝓝 0) :=
    hlog.const_div_atTop _
  refine tendsto_ell_sum_of_le (M := 2 * C1 * CL) (by positivity) hu fun η hη => ?_
  filter_upwards [hshape η hη, hA, hr.eventually_ge_atTop 3, hlog.eventually_gt_atTop 0]
    with n h1 h2 h3 h4
  set R : ℝ := r n with hRdef
  set L : ℝ := Real.log R with hLdef
  have hR0 : 0 < R := by linarith
  have hRL : 0 < R * L := mul_pos hR0 h4
  have hstep := tendsto_ell_sum_planar_step Y n R η (by linarith) h2 h1 Γ C1 hΓ'
  have hsum := hCL (2 * R) (by linarith)
  have hlog2 : Real.log (2 * R + 2) ≤ 2 * L := by
    calc Real.log (2 * R + 2) ≤ Real.log (R ^ 2) :=
          Real.log_le_log (by positivity) (by nlinarith)
      _ = 2 * L := by
          rw [Real.log_pow, hLdef]
          norm_num
  have hball : ∑ x ∈ ballFinset 2 (2 * R), (1 + euclidNorm x) ^ (-2 : ℝ) ≤ CL * (2 * L) := by
    have h5 : ∑ x ∈ ballFinset 2 (2 * R), (1 + euclidNorm x) ^ (-2 : ℝ) ≤
        CL * Real.log (2 * R + 2) := by simpa using hsum
    exact h5.trans (mul_le_mul_of_nonneg_left hlog2 hCLpos.le)
  have hstep' : |∑ x ∈ departureRange Y n, (localTime Y n x : ℝ) * Γ x -
      4 * ε * ∑ x ∈ ballFinset 2 R, (R - euclidNorm x) * Γ x| ≤ η * (2 * C1 * CL) * (R * L) := by
    refine hstep.trans ?_
    calc η * R * (C1 * ∑ x ∈ ballFinset 2 (2 * R), (1 + euclidNorm x) ^ (-2 : ℝ))
        ≤ η * R * (C1 * (CL * (2 * L))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hball hC1nn)
            (mul_nonneg hη.le hR0.le)
      _ = η * (2 * C1 * CL) * (R * L) := by ring
  have hT' := hCT R (by linarith)
  have hmain : |∑ x ∈ departureRange Y n, (localTime Y n x : ℝ) * Γ x - 4 * ε * c * R * L| ≤
      η * (2 * C1 * CL) * (R * L) + 4 * |ε| * CT * R := by
    calc |∑ x ∈ departureRange Y n, (localTime Y n x : ℝ) * Γ x - 4 * ε * c * R * L|
        = |(∑ x ∈ departureRange Y n, (localTime Y n x : ℝ) * Γ x -
            4 * ε * ∑ x ∈ ballFinset 2 R, (R - euclidNorm x) * Γ x) +
          4 * ε * (∑ x ∈ ballFinset 2 R, (R - euclidNorm x) * Γ x - c * R * L)| := by
            congr 1
            ring
      _ ≤ |∑ x ∈ departureRange Y n, (localTime Y n x : ℝ) * Γ x -
            4 * ε * ∑ x ∈ ballFinset 2 R, (R - euclidNorm x) * Γ x| +
          |4 * ε * (∑ x ∈ ballFinset 2 R, (R - euclidNorm x) * Γ x - c * R * L)| :=
            abs_add_le _ _
      _ ≤ η * (2 * C1 * CL) * (R * L) + 4 * |ε| * CT * R := by
          have h6 : |4 * ε * (∑ x ∈ ballFinset 2 R, (R - euclidNorm x) * Γ x - c * R * L)| ≤
              4 * |ε| * CT * R := by
            rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
            calc 4 * |ε| * |∑ x ∈ ballFinset 2 R, (R - euclidNorm x) * Γ x - c * R * L|
                ≤ 4 * |ε| * (CT * R) := by gcongr
              _ = 4 * |ε| * CT * R := by ring
          linarith
  have hdiv : (∑ x ∈ departureRange Y n, (localTime Y n x : ℝ) * Γ x) / (R * L) - 4 * ε * c =
      (∑ x ∈ departureRange Y n, (localTime Y n x : ℝ) * Γ x - 4 * ε * c * R * L) / (R * L) := by
    field_simp
  rw [hdiv, abs_div, abs_of_pos hRL, div_le_iff₀ hRL]
  calc |∑ x ∈ departureRange Y n, (localTime Y n x : ℝ) * Γ x - 4 * ε * c * R * L|
      ≤ η * (2 * C1 * CL) * (R * L) + 4 * |ε| * CT * R := hmain
    _ = (η * (2 * C1 * CL) + 4 * |ε| * CT / L) * (R * L) := by
        field_simp



/-! ### Scales -/

/-- `log x / x → 0` as `x → ∞`. -/
private theorem scale_tendsto_log_div_id :
    Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero

/-- `log log n / log n → 0`. -/
private theorem scale_tendsto_loglog_div_log :
    Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n) atTop (𝓝 0) :=
  scale_tendsto_log_div_id.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- `log n → ∞` along the naturals. -/
private theorem scale_tendsto_log_nat : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- The constant `A = (d+1)/(2 d ε ω_d)` with `r_n = (A n)^{1/(d+1)}`. -/
private noncomputable def scaleConst (d : ℕ) (ε : ℝ) : ℝ :=
  ((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d)

/-- The constant `A` is positive. -/
private theorem scale_const_pos (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) : 0 < scaleConst d ε := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  unfold scaleConst
  exact div_pos (by positivity) (mul_pos (mul_pos (mul_pos (by norm_num) hd0) hε)
    (unitBallVolume_pos d))

/-- `r_n = (A n)^{1/(d+1)}`. -/
private theorem scale_radius_eq (d : ℕ) (ε : ℝ) (n : ℕ) :
    radius d ε n = (scaleConst d ε * n) ^ ((1 : ℝ) / (d + 1)) := by
  unfold radius scaleConst
  congr 1
  ring

/-- `r_n → ∞`, the first of the scale lemmas. -/
private theorem radius_tendsto (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (radius d ε) atTop atTop := by
  have hq : 0 < (1 : ℝ) / (d + 1) := by positivity
  have hA := scale_const_pos hd hε
  have h1 : Tendsto (fun n : ℕ => scaleConst d ε * n) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hA
  have h2 := (tendsto_rpow_atTop hq).comp h1
  refine h2.congr fun n => ?_
  rw [scale_radius_eq]
  rfl

/-- For `n ≥ 1`, `log r_n = (log A + log n)/(d+1)`. -/
private theorem scale_log_radius (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    Real.log (radius d ε n) =
      (1 / ((d : ℝ) + 1)) * (Real.log (scaleConst d ε) + Real.log n) := by
  have hA := scale_const_pos hd hε
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [scale_radius_eq, Real.log_rpow (mul_pos hA hn0), Real.log_mul hA.ne' hn0.ne']

/-- `log r_n / log n → 1/(d+1)`. -/
private theorem scale_tendsto_log_radius_div_log (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => Real.log (radius d ε n) / Real.log n) atTop
      (𝓝 (1 / ((d : ℝ) + 1))) := by
  have h0 : Tendsto (fun n : ℕ => Real.log (scaleConst d ε) / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop scale_tendsto_log_nat
  have h1 : Tendsto (fun n : ℕ => (1 / ((d : ℝ) + 1)) *
      (Real.log (scaleConst d ε) / Real.log n + 1)) atTop
      (𝓝 ((1 / ((d : ℝ) + 1)) * (0 + 1))) :=
    (h0.add tendsto_const_nhds).const_mul _
  rw [zero_add, mul_one] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hlog : Real.log n ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    exact (Real.log_pos this).ne'
  rw [scale_log_radius hd hε (by omega)]
  field_simp

/-- `log r_n → ∞`. -/
private theorem scale_tendsto_log_radius (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => Real.log (radius d ε n)) atTop atTop :=
  Real.tendsto_log_atTop.comp (radius_tendsto hd hε)

/-- Eventually `σ_n² = r_n log r_n` in the plane and `σ_n² = r_n` otherwise. -/
private theorem scale_sigmaN_sq (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, sigmaN d ε n ^ 2 =
      if d = 2 then radius d ε n * Real.log (radius d ε n) else radius d ε n := by
  filter_upwards [(radius_tendsto hd hε).eventually_ge_atTop 1] with n hn
  unfold sigmaN
  split_ifs
  · exact Real.sq_sqrt (mul_nonneg (by linarith) (Real.log_nonneg hn))
  · exact Real.sq_sqrt (by linarith)

/-- `σ_n → ∞`. -/
private theorem sigmaN_tendsto (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (sigmaN d ε) atTop atTop := by
  unfold sigmaN
  split_ifs
  · exact Real.tendsto_sqrt_atTop.comp
      ((radius_tendsto hd hε).atTop_mul_atTop₀ (scale_tendsto_log_radius hd hε))
  · exact Real.tendsto_sqrt_atTop.comp (radius_tendsto hd hε)

/-- The law of the iterated logarithm scale is `√(2 σ_n² log log n)` for large `n`. -/
private theorem lilN_eq (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, lilN d ε n =
      Real.sqrt (2 * sigmaN d ε n ^ 2 * Real.log (Real.log n)) := by
  filter_upwards [scale_sigmaN_sq hd hε] with n hn
  rw [hn]
  unfold lilN
  split_ifs
  · congr 1
    ring
  · rfl

/-- `log log n → ∞`. -/
private theorem scale_tendsto_loglog_nat :
    Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
  Real.tendsto_log_atTop.comp scale_tendsto_log_nat

/-- `log σ_n² / log n → 1/(d+1)`. -/
private theorem scale_tendsto_log_sigmaN_sq_div_log (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => Real.log (sigmaN d ε n ^ 2) / Real.log n) atTop
      (𝓝 (1 / ((d : ℝ) + 1))) := by
  have hr := scale_tendsto_log_radius_div_log hd hε
  have hlogr := scale_tendsto_log_radius hd hε
  by_cases h2 : d = 2
  · have h3 : Tendsto (fun n : ℕ => Real.log (Real.log (radius d ε n)) / Real.log n) atTop
        (𝓝 0) := by
      have h := (scale_tendsto_log_div_id.comp hlogr).mul hr
      rw [zero_mul] at h
      refine h.congr' ?_
      filter_upwards [hlogr.eventually_gt_atTop 0] with n hn
      have hne : Real.log (radius d ε n) ≠ 0 := hn.ne'
      simp only [Function.comp]
      field_simp
    have h4 := hr.add h3
    rw [add_zero] at h4
    refine h4.congr' ?_
    filter_upwards [scale_sigmaN_sq hd hε, (radius_tendsto hd hε).eventually_gt_atTop 1] with n
      hn hr1
    have hlog : 0 < Real.log (radius d ε n) := Real.log_pos hr1
    rw [hn, if_pos h2, Real.log_mul (by linarith) hlog.ne', add_div]
  · refine hr.congr' ?_
    filter_upwards [scale_sigmaN_sq hd hε] with n hn
    rw [hn, if_neg h2]

/-- `log log σ_n² / log log n → 1`. -/
private theorem loglog_sigmaN (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => Real.log (Real.log (sigmaN d ε n ^ 2)) / Real.log (Real.log n))
      atTop (𝓝 1) := by
  have hq : 0 < 1 / ((d : ℝ) + 1) := by positivity
  have hu := scale_tendsto_log_sigmaN_sq_div_log hd hε
  have hlim : Tendsto (fun n : ℕ =>
      Real.log (Real.log (sigmaN d ε n ^ 2) / Real.log n) / Real.log (Real.log n) + 1)
      atTop (𝓝 (0 + 1)) :=
    ((hu.log hq.ne').div_atTop scale_tendsto_loglog_nat).add tendsto_const_nhds
  rw [zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [scale_tendsto_log_nat.eventually_gt_atTop 1,
    hu.eventually (lt_mem_nhds hq)] with n hn hpos
  have hlogn : 0 < Real.log n := by linarith
  have hlogne : Real.log n ≠ 0 := hlogn.ne'
  have hll : 0 < Real.log (Real.log n) := Real.log_pos hn
  have hc : (0 : ℝ) < Real.log (sigmaN d ε n ^ 2) / Real.log n := hpos
  have hmul : Real.log (sigmaN d ε n ^ 2) =
      (Real.log (sigmaN d ε n ^ 2) / Real.log n) * Real.log n := by
    field_simp
  conv_rhs => rw [hmul, Real.log_mul hc.ne' hlogne]
  field_simp

/-- Powers of `log (n + 2)` are negligible against positive powers of `r_n`. -/
private theorem scale_log_rpow_div_radius_rpow (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (a : ℝ)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.log (n + 2) ^ a / radius d ε n ^ c) atTop (𝓝 0) := by
  have hq : 0 < (1 : ℝ) / (d + 1) := by positivity
  have hA := scale_const_pos hd hε
  have h := (CERW.Support.Main.tendsto_log_rpow_div_rpow a
    (c := (1 / ((d : ℝ) + 1)) * c) (mul_pos hq hc)).div_const
    (scaleConst d ε ^ ((1 / ((d : ℝ) + 1)) * c))
  rw [zero_div] at h
  refine h.congr fun n => ?_
  rw [scale_radius_eq, ← Real.rpow_mul (mul_nonneg hA.le (Nat.cast_nonneg n)),
    Real.mul_rpow hA.le (Nat.cast_nonneg n), div_div, mul_comm]

/-- The normalizer is nonnegative. -/
private theorem scale_sigmaN_nonneg (d : ℕ) (ε : ℝ) (n : ℕ) : 0 ≤ sigmaN d ε n := by
  unfold sigmaN
  split_ifs <;> exact Real.sqrt_nonneg _

/-- For large `n`, `√r_n ≤ σ_n`. -/
private theorem scale_sqrt_radius_le_sigmaN (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.sqrt (radius d ε n) ≤ sigmaN d ε n := by
  filter_upwards [(scale_tendsto_log_radius hd hε).eventually_ge_atTop 1,
    (radius_tendsto hd hε).eventually_ge_atTop 1] with n h1 h2
  unfold sigmaN
  split_ifs
  · exact Real.sqrt_le_sqrt (le_mul_of_one_le_right (by linarith) h1)
  · exact le_rfl

/-- `log(n+2)³ / σ_n → 0`. -/
private theorem scale_log_cube_div_sigmaN (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => Real.log (n + 2) ^ 3 / sigmaN d ε n) atTop (𝓝 0) := by
  have h := scale_log_rpow_div_radius_rpow hd hε 3 (c := 1 / 2) (by norm_num)
  refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ h
  · have hlog : 0 ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    exact div_nonneg (pow_nonneg hlog 3) (scale_sigmaN_nonneg d ε n)
  · filter_upwards [scale_sqrt_radius_le_sigmaN hd hε,
      (radius_tendsto hd hε).eventually_gt_atTop 0] with n hn hr
    have hlog : 0 ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have hpos : 0 < Real.sqrt (radius d ε n) := Real.sqrt_pos.mpr hr
    have hcube : Real.log ((n : ℝ) + 2) ^ (3 : ℝ) = Real.log ((n : ℝ) + 2) ^ 3 := by
      simp
    rw [hcube, ← Real.sqrt_eq_rpow]
    exact div_le_div_of_nonneg_left (pow_nonneg hlog 3) hpos hn

/-- Planar case: `r_n^{1/2} √(log log n + 1) / σ_n → 0`. -/
private theorem scale_second_term_plane {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => radius 2 ε n ^ (((3 : ℝ) - ((2 : ℕ) : ℝ)) / 2) *
      Real.sqrt (Real.log (Real.log n) + 1) / sigmaN 2 ε n) atTop (𝓝 0) := by
  have hd : 2 ≤ 2 := le_rfl
  have hr := scale_tendsto_log_radius_div_log hd hε
  have hlogr := scale_tendsto_log_radius hd hε
  have hqne : (1 / (((2 : ℕ) : ℝ) + 1)) ≠ 0 := by norm_num
  have h1 : Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n + 1 / Real.log n) atTop
      (𝓝 (0 + 0)) :=
    scale_tendsto_loglog_div_log.add (tendsto_const_nhds.div_atTop scale_tendsto_log_nat)
  have h2 := h1.mul (hr.inv₀ hqne)
  rw [add_zero, zero_mul] at h2
  have h3 : Tendsto (fun n : ℕ => (Real.log (Real.log n) + 1) / Real.log (radius 2 ε n))
      atTop (𝓝 0) := by
    refine h2.congr' ?_
    filter_upwards [scale_tendsto_log_nat.eventually_gt_atTop 1,
      hlogr.eventually_gt_atTop 0] with n hn hpos
    have hlogn : Real.log n ≠ 0 := by linarith
    have hne : Real.log (radius 2 ε n) ≠ 0 := hpos.ne'
    field_simp
  have h4 := h3.sqrt
  rw [Real.sqrt_zero] at h4
  refine h4.congr' ?_
  filter_upwards [(radius_tendsto hd hε).eventually_gt_atTop 0, hlogr.eventually_gt_atTop 0]
    with n hr0 hlog
  have hexp : (((3 : ℝ) - ((2 : ℕ) : ℝ)) / 2) = 1 / 2 := by norm_num
  have hsqrt : 0 < Real.sqrt (radius 2 ε n) := Real.sqrt_pos.mpr hr0
  unfold sigmaN
  rw [if_pos rfl, hexp, ← Real.sqrt_eq_rpow, Real.sqrt_mul hr0.le,
    mul_div_mul_left _ _ hsqrt.ne', ← Real.sqrt_div' _ hlog.le]

/-- Dimension at least three: `r_n^{(3-d)/2} √(log log n + 1) / σ_n → 0`. -/
private theorem scale_second_term_high (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => radius d ε n ^ (((3 : ℝ) - d) / 2) *
      Real.sqrt (Real.log (Real.log n) + 1) / sigmaN d ε n) atTop (𝓝 0) := by
  have hd2 : 2 ≤ d := by omega
  have hne : d ≠ 2 := by omega
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h := scale_log_rpow_div_radius_rpow hd2 hε (1 / 2) (c := 1 / 2) (by norm_num)
  refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ h
  · have hr : 0 ≤ radius d ε n := by
      rw [scale_radius_eq]
      exact Real.rpow_nonneg (mul_nonneg (scale_const_pos hd2 hε).le (Nat.cast_nonneg n)) _
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg hr _) (Real.sqrt_nonneg _))
      (scale_sigmaN_nonneg d ε n)
  · filter_upwards [(radius_tendsto hd2 hε).eventually_ge_atTop 1,
      scale_tendsto_log_nat.eventually_gt_atTop 0] with n hr1 hlogn
    have hr0 : 0 < radius d ε n := by linarith
    have hsig : sigmaN d ε n = Real.sqrt (radius d ε n) := by
      unfold sigmaN
      rw [if_neg hne]
    have hpow : radius d ε n ^ (((3 : ℝ) - d) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hr1 (by linarith)
    have hll : Real.log (Real.log n) + 1 ≤ Real.log ((n : ℝ) + 2) := by
      have h1 := Real.log_le_sub_one_of_pos hlogn
      have h2 : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 2) := by
        have hn : (0 : ℝ) < n := by
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · subst h0
            simp at hlogn
          · exact_mod_cast h0
        exact Real.log_le_log hn (by linarith)
      linarith
    have hsq : Real.sqrt (Real.log (Real.log n) + 1) ≤ Real.sqrt (Real.log ((n : ℝ) + 2)) :=
      Real.sqrt_le_sqrt hll
    rw [hsig, ← Real.sqrt_eq_rpow (radius d ε n)]
    have hsq' : Real.sqrt (Real.log (Real.log n) + 1) ≤
        Real.log ((n : ℝ) + 2) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow]
      exact hsq
    have hnum : radius d ε n ^ (((3 : ℝ) - d) / 2) * Real.sqrt (Real.log (Real.log n) + 1) ≤
        Real.log ((n : ℝ) + 2) ^ ((1 : ℝ) / 2) := by
      calc radius d ε n ^ (((3 : ℝ) - d) / 2) * Real.sqrt (Real.log (Real.log n) + 1)
          ≤ 1 * Real.log ((n : ℝ) + 2) ^ ((1 : ℝ) / 2) :=
            mul_le_mul hpow hsq' (Real.sqrt_nonneg _) zero_le_one
        _ = Real.log ((n : ℝ) + 2) ^ ((1 : ℝ) / 2) := one_mul _
    exact div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg _)

/-- The error scale is negligible against the normalizer. -/
private theorem errScale_div_sigmaN (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => errScale d ε n / sigmaN d ε n) atTop (𝓝 0) := by
  have hsecond : Tendsto (fun n : ℕ => radius d ε n ^ (((3 : ℝ) - d) / 2) *
      Real.sqrt (Real.log (Real.log n) + 1) / sigmaN d ε n) atTop (𝓝 0) := by
    by_cases h2 : d = 2
    · subst h2
      exact scale_second_term_plane hε
    · exact scale_second_term_high (by omega) hε
  have h := (scale_log_cube_div_sigmaN hd hε).add hsecond
  rw [add_zero] at h
  refine h.congr fun n => ?_
  rw [errScale, add_div]


/-- If `ρ_n → c > 0` and `σ_n² → ∞` then `log log (ρ_n σ_n²) / log log σ_n² → 1`. -/
private theorem lil_of_bracket_loglog_ratio (σ W : ℕ → ℝ) (hσ : Tendsto σ atTop atTop)
    (c : ℝ) (hc : 0 < c) (hW : Tendsto (fun n => W n / σ n ^ 2) atTop (𝓝 c)) :
    Tendsto (fun n => Real.log (Real.log (W n)) / Real.log (Real.log (σ n ^ 2))) atTop (𝓝 1) := by
  have hσ2 : Tendsto (fun n => σ n ^ 2) atTop atTop :=
    (tendsto_pow_atTop (two_ne_zero)).comp hσ
  have hLa : Tendsto (fun n => Real.log (σ n ^ 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp hσ2
  have hLLa : Tendsto (fun n => Real.log (Real.log (σ n ^ 2))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLa
  have hσpos : ∀ᶠ n in atTop, 0 < σ n := hσ.eventually_gt_atTop 0
  have hρpos : ∀ᶠ n in atTop, 0 < W n / σ n ^ 2 := hW.eventually (lt_mem_nhds hc)
  have hLapos : ∀ᶠ n in atTop, 0 < Real.log (σ n ^ 2) := hLa.eventually_gt_atTop 0
  have hLLapos : ∀ᶠ n in atTop, 0 < Real.log (Real.log (σ n ^ 2)) := hLLa.eventually_gt_atTop 0
  -- `log W / log σ² → 1`
  have hlogρ : Tendsto (fun n => Real.log (W n / σ n ^ 2)) atTop (𝓝 (Real.log c)) :=
    hW.log hc.ne'
  have hq1 : Tendsto (fun n => Real.log (W n / σ n ^ 2) / Real.log (σ n ^ 2)) atTop (𝓝 0) :=
    hlogρ.div_atTop hLa
  have hq2 : Tendsto (fun n => Real.log (W n) / Real.log (σ n ^ 2)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n => 1 + Real.log (W n / σ n ^ 2) / Real.log (σ n ^ 2)) atTop
        (𝓝 (1 + 0)) := tendsto_const_nhds.add hq1
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [hσpos, hρpos, hLapos] with n hs hr hl
    have hs2 : σ n ^ 2 ≠ 0 := by positivity
    have hWn : W n = W n / σ n ^ 2 * σ n ^ 2 := by field_simp
    have hlog : Real.log (W n) = Real.log (W n / σ n ^ 2) + Real.log (σ n ^ 2) := by
      conv_lhs => rw [hWn]
      rw [Real.log_mul hr.ne' hs2]
    rw [hlog]
    field_simp
    ring
  -- `log (log W / log σ²) → 0`
  have hq3 : Tendsto (fun n => Real.log (Real.log (W n) / Real.log (σ n ^ 2))) atTop (𝓝 0) := by
    have := hq2.log one_ne_zero
    rwa [Real.log_one] at this
  have hq4 : Tendsto (fun n => Real.log (Real.log (W n) / Real.log (σ n ^ 2)) /
      Real.log (Real.log (σ n ^ 2))) atTop (𝓝 0) := hq3.div_atTop hLLa
  have h1 : Tendsto (fun n => 1 + Real.log (Real.log (W n) / Real.log (σ n ^ 2)) /
      Real.log (Real.log (σ n ^ 2))) atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add hq4
  rw [add_zero] at h1
  refine h1.congr' ?_
  have hWpos : ∀ᶠ n in atTop, 0 < Real.log (W n) / Real.log (σ n ^ 2) := hq2.eventually
    (lt_mem_nhds one_pos)
  filter_upwards [hLapos, hLLapos, hWpos] with n hl hll hw
  have hlogW : 0 < Real.log (W n) := by
    have := mul_pos hw hl
    rwa [div_mul_cancel₀ _ hl.ne'] at this
  have hsplit : Real.log (Real.log (W n)) =
      Real.log (Real.log (W n) / Real.log (σ n ^ 2)) + Real.log (Real.log (σ n ^ 2)) := by
    rw [← Real.log_mul hw.ne' hl.ne', div_mul_cancel₀ _ hl.ne']
  rw [hsplit]
  field_simp
  ring

/-- The ratio `√(2 W log log W) / lil` tends to `√c`. -/
private theorem lil_of_bracket_sqrt_ratio (σ lil W : ℕ → ℝ) (hσ : Tendsto σ atTop atTop)
    (hlil : ∀ᶠ n : ℕ in atTop, lil n = Real.sqrt (2 * σ n ^ 2 * Real.log (Real.log n)))
    (hloglog : Tendsto (fun n : ℕ => Real.log (Real.log (σ n ^ 2)) / Real.log (Real.log n))
      atTop (𝓝 1))
    (c : ℝ) (hc : 0 < c) (hW : Tendsto (fun n => W n / σ n ^ 2) atTop (𝓝 c)) :
    Tendsto (fun n => Real.sqrt (2 * W n * Real.log (Real.log (W n))) / lil n) atTop
      (𝓝 (Real.sqrt c)) := by
  have hσ2 : Tendsto (fun n => σ n ^ 2) atTop atTop :=
    (tendsto_pow_atTop (two_ne_zero)).comp hσ
  have hLa : Tendsto (fun n => Real.log (σ n ^ 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp hσ2
  have hLLa : Tendsto (fun n => Real.log (Real.log (σ n ^ 2))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLa
  have hratio := lil_of_bracket_loglog_ratio σ W hσ c hc hW
  have hprod : Tendsto (fun n : ℕ => Real.log (Real.log (W n)) / Real.log (Real.log (σ n ^ 2)) *
      (Real.log (Real.log (σ n ^ 2)) / Real.log (Real.log n))) atTop (𝓝 (1 * 1)) :=
    hratio.mul hloglog
  rw [one_mul] at hprod
  have hLLapos : ∀ᶠ n in atTop, 0 < Real.log (Real.log (σ n ^ 2)) := hLLa.eventually_gt_atTop 0
  have hlog2 : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlogpos : ∀ᶠ n : ℕ in atTop, 0 < Real.log (Real.log n) := hlog2.eventually_gt_atTop 0
  have hσpos : ∀ᶠ n in atTop, 0 < σ n := hσ.eventually_gt_atTop 0
  have hk : Tendsto (fun n : ℕ => Real.log (Real.log (W n)) / Real.log (Real.log n)) atTop
      (𝓝 1) := by
    refine hprod.congr' ?_
    filter_upwards [hLLapos] with n hll
    rw [div_mul_div_cancel₀ hll.ne']
  have hmain : Tendsto (fun n => Real.sqrt (W n / σ n ^ 2 *
      (Real.log (Real.log (W n)) / Real.log (Real.log n)))) atTop
      (𝓝 (Real.sqrt (c * 1))) := (hW.mul hk).sqrt
  rw [mul_one] at hmain
  refine hmain.congr' ?_
  filter_upwards [hlil, hlogpos, hσpos] with n hl hlp hs
  have hs2 : 0 < σ n ^ 2 := by positivity
  have hden : 0 ≤ 2 * σ n ^ 2 * Real.log (Real.log n) := by positivity
  rw [hl, ← Real.sqrt_div' _ hden]
  congr 1
  field_simp

/-- For `W_n → ∞`, `√(log log max (W_n, e^e)) / √W_n → 0`. -/
private theorem lil_of_bracket_sqrt_loglog_div (W : ℕ → ℝ) (hW : Tendsto W atTop atTop) :
    Tendsto (fun n => Real.sqrt (Real.log (Real.log (max (W n) (Real.exp (Real.exp 1))))) /
      Real.sqrt (W n)) atTop (𝓝 0) := by
  have hlw : Tendsto (fun n => Real.log (W n) / W n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hW
  have hbig : ∀ᶠ n in atTop, Real.exp (Real.exp 1) ≤ W n := hW.eventually_ge_atTop _
  have hW0 : ∀ᶠ n in atTop, 0 < W n := hW.eventually_gt_atTop 0
  have hsq : Tendsto (fun n => Real.sqrt (Real.log (W n) / W n)) atTop (𝓝 (Real.sqrt 0)) :=
    hlw.sqrt
  rw [Real.sqrt_zero] at hsq
  have hup : ∀ᶠ n in atTop, Real.sqrt (Real.log (Real.log (max (W n)
      (Real.exp (Real.exp 1))))) / Real.sqrt (W n) ≤ Real.sqrt (Real.log (W n) / W n) := by
    filter_upwards [hbig, hW0] with n hb hw
    have he : Real.exp 1 ≤ Real.log (W n) := by
      rw [Real.le_log_iff_exp_le hw]
      exact hb
    have hl1 : 1 ≤ Real.log (W n) := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hlpos : 0 < Real.log (W n) := by linarith
    rw [max_eq_left hb, ← Real.sqrt_div (Real.log_nonneg hl1)]
    refine Real.sqrt_le_sqrt ?_
    refine div_le_div_of_nonneg_right ?_ hw.le
    linarith [Real.log_le_sub_one_of_pos hlpos]
  refine squeeze_zero' ?_ hup hsq
  exact Filter.Eventually.of_forall fun n => by positivity

/-- Conversion of the two-sided comparison with `√(2 W log log W)` into the statement with
`lil`: if `R_n / lil_n → s > 0`, `lil_n > 0` eventually, `T_n ≤ (1 + δ') R_n` eventually and
`(1 - δ') R_n ≤ T_n` frequently for every `δ' > 0`, then the conclusion of the lemma holds. -/
private theorem lil_of_bracket_convert (T R lil : ℕ → ℝ) (s : ℝ) (hs : 0 < s)
    (hq : Tendsto (fun n => R n / lil n) atTop (𝓝 s)) (hpos : ∀ᶠ n in atTop, 0 < lil n)
    (hup : ∀ δ' : ℝ, 0 < δ' → ∀ᶠ n in atTop, T n ≤ (1 + δ') * R n)
    (hlo : ∀ δ' : ℝ, 0 < δ' → ∃ᶠ n in atTop, (1 - δ') * R n ≤ T n) (δ : ℝ) (hδ : 0 < δ) :
    (∀ᶠ n in atTop, T n ≤ (s + δ) * lil n) ∧ (∃ᶠ n in atTop, (s - δ) * lil n ≤ T n) := by
  set δ' : ℝ := δ / (2 * s + δ) with hδ'
  have hden : 0 < 2 * s + δ := by linarith
  have hδ'pos : 0 < δ' := div_pos hδ hden
  have hδ'lt : δ' ≤ 1 := by
    rw [hδ', div_le_one hden]
    linarith
  have hqup : ∀ᶠ n in atTop, R n / lil n ≤ s + δ / 2 :=
    (hq.eventually (Iio_mem_nhds (show s < s + δ / 2 by linarith))).mono fun _ hx => le_of_lt hx
  have hqlo : ∀ᶠ n in atTop, s - δ / 2 ≤ R n / lil n :=
    (hq.eventually (Ioi_mem_nhds (show s - δ / 2 < s by linarith))).mono fun _ hx => le_of_lt hx
  constructor
  · filter_upwards [hup δ' hδ'pos, hqup, hpos] with n h1 h2 h3
    have hR : R n ≤ (s + δ / 2) * lil n := by
      rw [div_le_iff₀ h3] at h2
      exact h2
    have hcoef : (1 + δ') * (s + δ / 2) = s + δ := by
      rw [hδ']
      field_simp
      ring
    calc T n ≤ (1 + δ') * R n := h1
      _ ≤ (1 + δ') * ((s + δ / 2) * lil n) :=
          mul_le_mul_of_nonneg_left hR (by linarith)
      _ = (s + δ) * lil n := by rw [← mul_assoc, hcoef]
  · have hfr := hlo δ' hδ'pos
    refine (hfr.and_eventually (hqlo.and hpos)).mono ?_
    rintro n ⟨h1, h2, h3⟩
    have hR : (s - δ / 2) * lil n ≤ R n := by
      rw [le_div_iff₀ h3] at h2
      exact h2
    have hcoef : s - δ ≤ (1 - δ') * (s - δ / 2) := by
      rw [hδ']
      have : (1 - δ / (2 * s + δ)) * (s - δ / 2) - (s - δ) =
          δ * δ / (2 * s + δ) := by
        field_simp
        ring
      have hnn : 0 ≤ δ * δ / (2 * s + δ) := by positivity
      linarith
    calc (s - δ) * lil n ≤ ((1 - δ') * (s - δ / 2)) * lil n :=
          mul_le_mul_of_nonneg_right hcoef h3.le
      _ = (1 - δ') * ((s - δ / 2) * lil n) := by ring
      _ ≤ (1 - δ') * R n := mul_le_mul_of_nonneg_left hR (by linarith)
      _ ≤ T n := h1

/-- The law of the iterated logarithm of Stout, for a martingale with a.s. bounded increments
whose bracket is asymptotic to a constant multiple of `σ_n²`. -/
private theorem lil_of_bracket (hLIL : StoutLIL.{u})
    {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (S : ℕ → Ω → ℝ) (hS : Martingale S ℱ μ)
    (hL2 : ∀ n, MemLp (S n) 2 μ) (h0 : ∀ ω, S 0 ω = 0) (K : ℝ)
    (hK : ∀ᵐ ω ∂μ, ∀ n, |S (n + 1) ω - S n ω| ≤ K) (σ lil : ℕ → ℝ)
    (hσ : Tendsto σ atTop atTop)
    (hlil : ∀ᶠ n : ℕ in atTop, lil n = Real.sqrt (2 * σ n ^ 2 * Real.log (Real.log n)))
    (hloglog : Tendsto (fun n : ℕ => Real.log (Real.log (σ n ^ 2)) / Real.log (Real.log n))
      atTop (𝓝 1))
    (c : ℝ) (hc : 0 < c)
    (hbr : ∀ᵐ ω ∂μ, Tendsto (fun n => CERW.predBracket μ ℱ S S n ω / σ n ^ 2) atTop (𝓝 c)) :
    ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ →
      (∀ᶠ n in atTop, S n ω ≤ (Real.sqrt c + δ) * lil n) ∧
      (∃ᶠ n in atTop, (Real.sqrt c - δ) * lil n ≤ S n ω) := by
  have hσ2 : Tendsto (fun n => σ n ^ 2) atTop atTop :=
    (tendsto_pow_atTop (two_ne_zero)).comp hσ
  have hσpos : ∀ᶠ n in atTop, 0 < σ n := hσ.eventually_gt_atTop 0
  have hW : ∀ᵐ ω ∂μ, Tendsto (fun n => CERW.predBracket μ ℱ S S n ω) atTop atTop := by
    filter_upwards [hbr] with ω hω
    have h1 : Tendsto (fun n => CERW.predBracket μ ℱ S S n ω / σ n ^ 2 * σ n ^ 2) atTop atTop :=
      hω.pos_mul_atTop hc hσ2
    refine h1.congr' ?_
    filter_upwards [hσpos] with n hs
    have : σ n ^ 2 ≠ 0 := by positivity
    field_simp
  have hB : ∀ n, StronglyMeasurable[ℱ n] ((fun (_ : ℕ) (_ : Ω) => K) (n + 1)) :=
    fun n => stronglyMeasurable_const
  have hB2 : ∀ᵐ ω ∂μ, ∀ n, |S (n + 1) ω - S n ω| ≤ (fun (_ : ℕ) (_ : Ω) => K) (n + 1) ω := hK
  have hB3 : ∀ᵐ ω ∂μ, Tendsto (fun n => (fun (_ : ℕ) (_ : Ω) => K) n ω *
      Real.sqrt (Real.log (Real.log (max (CERW.predBracket μ ℱ S S n ω)
        (Real.exp (Real.exp 1))))) / Real.sqrt (CERW.predBracket μ ℱ S S n ω)) atTop (𝓝 0) := by
    filter_upwards [hW] with ω hω
    have := (lil_of_bracket_sqrt_loglog_div (fun n => CERW.predBracket μ ℱ S S n ω) hω).const_mul K
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    ring
  have hstout := hLIL μ ℱ S hS hL2 h0 (fun _ _ => K) hB hB2 hW hB3
  filter_upwards [hstout, hbr] with ω hω hωbr δ hδ
  set W : ℕ → ℝ := fun n => CERW.predBracket μ ℱ S S n ω with hWdef
  have hratio := lil_of_bracket_sqrt_ratio σ lil W hσ hlil hloglog c hc hωbr
  have hpos : ∀ᶠ n in atTop, 0 < lil n := by
    have hlog2 : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
      Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    filter_upwards [hlil, hσpos, hlog2.eventually_gt_atTop 0] with n hl hs hll
    rw [hl]
    exact Real.sqrt_pos.mpr (by positivity)
  exact lil_of_bracket_convert (fun n => S n ω) (fun n => Real.sqrt (2 * W n *
    Real.log (Real.log (W n)))) lil (Real.sqrt c) (Real.sqrt_pos.mpr hc) hratio hpos
    (fun δ' hδ' => (hω δ' hδ').1) (fun δ' hδ' => (hω δ' hδ').2) δ hδ


/-- If `f n` is almost everywhere equal to `g` for all large `n`, then `f n → g` in measure. -/
private theorem tendstoInDistribution_tendstoInMeasure_of_eventually_ae_eq {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (h : ∀ᶠ n in atTop, f n =ᵐ[μ] g) : TendstoInMeasure μ f atTop g := by
  intro ε hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [h] with n hn
  symm
  refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hn)
  intro hω'
  have hω2 : ε ≤ edist (f n ω) (g ω) := hω
  rw [hω', edist_self] at hω2
  exact hε.ne' (nonpos_iff_eq_zero.1 hω2)

/-- A predictable bracket is almost everywhere strongly measurable, being a finite sum of
conditional expectations. -/
private theorem tendstoInDistribution_aestronglyMeasurable_predBracket {Ω : Type*}
    [m0 : MeasurableSpace Ω] (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S : ℕ → Ω → ℝ) (n : ℕ) :
    AEStronglyMeasurable (CERW.predBracket μ ℱ S S n) μ := by
  have h := Finset.stronglyMeasurable_sum (Finset.range n)
    (f := fun t => μ[fun ω => (S (t + 1) ω - S t ω) * (S (t + 1) ω - S t ω) | ℱ t])
    fun t _ => stronglyMeasurable_condExp.mono (ℱ.le t)
  exact (h.aestronglyMeasurable).congr (Filter.Eventually.of_forall fun ω => by
    simp [CERW.predBracket])

/-- The law of `z ↦ ⟪z, t⟫` under a centered multivariate Gaussian is the centered real
Gaussian with variance `t ⬝ᵥ C *ᵥ t`. -/
private theorem tendstoInDistribution_map_inner_multivariateGaussian {k : ℕ}
    (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) (t : EuclideanSpace ℝ (Fin k)) :
    (multivariateGaussian 0 C).map (fun z => inner ℝ z t) =
      gaussianReal 0 (∑ i, ∑ j, t i * C i j * t j).toNNReal := by
  have hL := IsGaussian.map_eq_gaussianReal (μ := multivariateGaussian 0 C) (innerSL ℝ t)
  have hfun : (fun z : EuclideanSpace ℝ (Fin k) => inner ℝ z t) = innerSL ℝ t := by
    funext z
    simp [real_inner_comm]
  have hvar : Var[⇑(innerSL ℝ t); multivariateGaussian 0 C] = ∑ i, ∑ j, t i * C i j * t j := by
    have h1 := covarianceBilin_self (μ := multivariateGaussian 0 C) IsGaussian.memLp_two_id t
    rw [covarianceBilin_multivariateGaussian hC] at h1
    have h2 : (fun u : EuclideanSpace ℝ (Fin k) => inner ℝ t u) = ⇑(innerSL ℝ t) := by
      funext u
      simp
    rw [h2] at h1
    rw [← h1]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hfun, hL, hvar, (innerSL ℝ t).integral_comp_id_comm IsGaussian.integrable_id]
  simp

/-- The martingale central limit theorem for a martingale with bounded increments, whose
predictable bracket divided by `σ_n²` converges almost surely to `c`. -/
private theorem tendstoInDistribution_of_bracket (hCLT : MartingaleCLT.{u})
    {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (S : ℕ → Ω → ℝ) (hS : Martingale S ℱ μ)
    (hL2 : ∀ n, MemLp (S n) 2 μ) (h0 : ∀ ω, S 0 ω = 0) (K : ℝ)
    (hK : ∀ᵐ ω ∂μ, ∀ n, |S (n + 1) ω - S n ω| ≤ K) (σ : ℕ → ℝ)
    (hσ : Tendsto σ atTop atTop) (c : ℝ≥0)
    (hbr : ∀ᵐ ω ∂μ, Tendsto (fun n => CERW.predBracket μ ℱ S S n ω / σ n ^ 2) atTop
      (𝓝 (c : ℝ))) :
    TendstoInDistribution (fun n ω => S n ω / σ n) atTop id (fun _ => μ) (gaussianReal 0 c) := by
  set s : ℕ → ℝ := fun n => max (σ n) 1 with hs
  have hs_pos : ∀ n, 0 < s n := fun n => lt_of_lt_of_le one_pos (le_max_right _ _)
  have hs_top : Tendsto s atTop atTop :=
    tendsto_atTop_mono (fun n => le_max_left _ _) hσ
  have hσs : ∀ᶠ n in atTop, σ n = s n := by
    filter_upwards [hσ.eventually_ge_atTop 1] with n hn
    simp [hs, hn]
  have hlind : ∀ δ : ℝ, 0 < δ → TendstoInMeasure μ
      (fun n => ∑ i ∈ Finset.range n,
        μ[fun ω => ((S (i + 1) ω - S i ω) / s n) ^ 2 *
          (if δ < |S (i + 1) ω - S i ω| / s n then 1 else 0) | ℱ i])
      atTop (fun _ => 0) := by
    intro δ hδ
    refine tendstoInDistribution_tendstoInMeasure_of_eventually_ae_eq ?_
    filter_upwards [hs_top.eventually_gt_atTop (K / δ)] with n hn
    have hKn : K < δ * s n := by
      have := (div_lt_iff₀ hδ).1 hn
      linarith
    have hzero : ∀ i, μ[fun ω => ((S (i + 1) ω - S i ω) / s n) ^ 2 *
          (if δ < |S (i + 1) ω - S i ω| / s n then 1 else 0) | ℱ i] =ᵐ[μ] 0 := by
      intro i
      have hae : (fun ω => ((S (i + 1) ω - S i ω) / s n) ^ 2 *
          (if δ < |S (i + 1) ω - S i ω| / s n then 1 else 0)) =ᵐ[μ] 0 := by
        filter_upwards [hK] with ω hω
        have hle : |S (i + 1) ω - S i ω| / s n ≤ δ := by
          rw [div_le_iff₀ (hs_pos n)]
          nlinarith [hω i]
        simp [not_lt.2 hle]
      exact (condExp_congr_ae hae).trans (by simp)
    have hall : ∀ᵐ ω ∂μ, ∀ i, μ[fun ω => ((S (i + 1) ω - S i ω) / s n) ^ 2 *
          (if δ < |S (i + 1) ω - S i ω| / s n then 1 else 0) | ℱ i] ω = 0 :=
      ae_all_iff.2 hzero
    filter_upwards [hall] with ω hω
    rw [Finset.sum_apply]
    exact Finset.sum_eq_zero fun i _ => hω i
  have hbr' : TendstoInMeasure μ
      (fun n => fun ω => CERW.predBracket μ ℱ S S n ω / s n ^ 2) atTop (fun _ => (c : ℝ)) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
    · have h := tendstoInDistribution_aestronglyMeasurable_predBracket μ ℱ S n
      fun_prop
    · filter_upwards [hbr] with ω hω
      refine hω.congr' ?_
      filter_upwards [hσs] with n hn
      rw [hn]
  have hX := hCLT μ ℱ S hS hL2 h0 s hs_pos c hlind hbr'
  have hmeas : ∀ n, AEMeasurable (fun ω => S n ω / σ n) μ := fun n =>
    (((hS.1 n).mono (ℱ.le n)).aemeasurable).div_const _
  refine tendstoInDistribution_of_tendstoInMeasure_sub (fun n ω => S n ω / σ n) id hX ?_ hmeas
  refine tendstoInDistribution_tendstoInMeasure_of_eventually_ae_eq ?_
  filter_upwards [hσs] with n hn
  refine Filter.Eventually.of_forall fun ω => ?_
  simp [hn]

/-- Cramér–Wold: a random vector whose every projection is asymptotically Gaussian with
variance `t ⬝ᵥ C *ᵥ t` converges in distribution to the multivariate Gaussian `N(0, C)`. -/
private theorem tendstoInDistribution_vector {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {k : ℕ} (V : ℕ → Ω → EuclideanSpace ℝ (Fin k))
    (hV : ∀ n, AEMeasurable (V n) μ) (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (h : ∀ t : Fin k → ℝ, TendstoInDistribution (fun n ω => ∑ i, t i * V n ω i) atTop id
      (fun _ => μ) (gaussianReal 0 (∑ i, ∑ j, t i * C i j * t j).toNNReal)) :
    TendstoInDistribution V atTop id (fun _ => μ) (multivariateGaussian 0 C) := by
  refine LatticeProb.CramerWold.tendstoInDistribution_of_forall_inner V id μ
    (multivariateGaussian 0 C) hV aemeasurable_id fun t => ?_
  have hproj : ∀ z : EuclideanSpace ℝ (Fin k), inner ℝ z t = ∑ i, t i * z i := by
    intro z
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  have h1 := h (fun i => t i)
  have h2 := LatticeProb.CramerWold.tendstoInDistribution_of_map_eq h1
    (fun z : EuclideanSpace ℝ (Fin k) => inner ℝ (id z) t) (by fun_prop)
    (tendstoInDistribution_map_inner_multivariateGaussian C hC t)
  simpa only [hproj] using h2

/-! ### The bracket of a Dynkin martingale -/

/-- A weighted sum of squares about a nearly uniform probability vector: if `p` is a probability
vector on `s` with `|p i - 1/N| ≤ θ` and `|a i| ≤ B`, where `N = |s|`, then the variance of `a`
under `p` differs from its variance under the uniform weights by at most `3 N θ B²`. -/
private theorem abs_var_sub_le {ι : Type*} (s : Finset ι) {N θ B : ℝ} (hN : (s.card : ℝ) = N)
    (hNpos : 0 < N) (p a : ι → ℝ) (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∑ i ∈ s, p i = 1)
    (hpθ : ∀ i ∈ s, |p i - 1 / N| ≤ θ) (ha : ∀ i ∈ s, |a i| ≤ B) (hB : 0 ≤ B) (hθ : 0 ≤ θ) :
    |(∑ i ∈ s, p i * a i ^ 2 - (∑ i ∈ s, p i * a i) ^ 2) -
        ((1 / N) * ∑ i ∈ s, a i ^ 2 - ((1 / N) * ∑ i ∈ s, a i) ^ 2)| ≤ 3 * N * θ * B ^ 2 := by
  have hsq : |∑ i ∈ s, p i * a i ^ 2 - (1 / N) * ∑ i ∈ s, a i ^ 2| ≤ N * θ * B ^ 2 := by
    have h1 : ∑ i ∈ s, p i * a i ^ 2 - (1 / N) * ∑ i ∈ s, a i ^ 2 =
        ∑ i ∈ s, (p i - 1 / N) * a i ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1]
    calc |∑ i ∈ s, (p i - 1 / N) * a i ^ 2| ≤ ∑ i ∈ s, |(p i - 1 / N) * a i ^ 2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ s, θ * B ^ 2 := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [abs_mul, abs_of_nonneg (sq_nonneg (a i))]
          have h2 : a i ^ 2 ≤ B ^ 2 := by
            rw [← sq_abs (a i)]
            exact pow_le_pow_left₀ (abs_nonneg _) (ha i hi) 2
          exact mul_le_mul (hpθ i hi) h2 (sq_nonneg _) hθ
      _ = N * θ * B ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, hN]
          ring
  have hlin : |∑ i ∈ s, p i * a i - (1 / N) * ∑ i ∈ s, a i| ≤ N * θ * B := by
    have h1 : ∑ i ∈ s, p i * a i - (1 / N) * ∑ i ∈ s, a i =
        ∑ i ∈ s, (p i - 1 / N) * a i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1]
    calc |∑ i ∈ s, (p i - 1 / N) * a i| ≤ ∑ i ∈ s, |(p i - 1 / N) * a i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ s, θ * B := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [abs_mul]
          exact mul_le_mul (hpθ i hi) (ha i hi) (abs_nonneg _) hθ
      _ = N * θ * B := by
          rw [Finset.sum_const, nsmul_eq_mul, hN]
          ring
  have hm : |∑ i ∈ s, p i * a i| ≤ B := by
    calc |∑ i ∈ s, p i * a i| ≤ ∑ i ∈ s, |p i * a i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ s, p i * B := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [abs_mul, abs_of_nonneg (hp0 i hi)]
          exact mul_le_mul_of_nonneg_left (ha i hi) (hp0 i hi)
      _ = B := by rw [← Finset.sum_mul, hp1, one_mul]
  have hm0 : |(1 / N) * ∑ i ∈ s, a i| ≤ B := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / N)]
    calc 1 / N * |∑ i ∈ s, a i| ≤ 1 / N * ∑ i ∈ s, |a i| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ ≤ 1 / N * ∑ _i ∈ s, B :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ha i hi) (by positivity)
      _ = B := by
          rw [Finset.sum_const, nsmul_eq_mul, hN]
          field_simp
  set m := ∑ i ∈ s, p i * a i with hmdef
  set m0 := (1 / N) * ∑ i ∈ s, a i with hm0def
  have hsqdiff : |m ^ 2 - m0 ^ 2| ≤ 2 * N * θ * B ^ 2 := by
    have h1 : m ^ 2 - m0 ^ 2 = (m - m0) * (m + m0) := by ring
    rw [h1, abs_mul]
    have h2 : |m + m0| ≤ 2 * B := by
      calc |m + m0| ≤ |m| + |m0| := abs_add_le _ _
        _ ≤ B + B := add_le_add hm hm0
        _ = 2 * B := by ring
    calc |m - m0| * |m + m0| ≤ (N * θ * B) * (2 * B) :=
          mul_le_mul hlin h2 (abs_nonneg _) (by positivity)
      _ = 2 * N * θ * B ^ 2 := by ring
  have hsplit : (∑ i ∈ s, p i * a i ^ 2 - m ^ 2) -
      ((1 / N) * ∑ i ∈ s, a i ^ 2 - m0 ^ 2) =
      (∑ i ∈ s, p i * a i ^ 2 - (1 / N) * ∑ i ∈ s, a i ^ 2) - (m ^ 2 - m0 ^ 2) := by ring
  rw [hsplit]
  calc |(∑ i ∈ s, p i * a i ^ 2 - (1 / N) * ∑ i ∈ s, a i ^ 2) - (m ^ 2 - m0 ^ 2)|
      ≤ |∑ i ∈ s, p i * a i ^ 2 - (1 / N) * ∑ i ∈ s, a i ^ 2| + |m ^ 2 - m0 ^ 2| :=
        abs_sub _ _
    _ ≤ N * θ * B ^ 2 + 2 * N * θ * B ^ 2 := add_le_add hsq hsqdiff
    _ = 3 * N * θ * B ^ 2 := by ring


/-- The conditional variance of the increment of the Dynkin martingale of `f` at time `t`, read
from the path `x`: `Σ_e p_t(e) (f(x_t + e) - f(x_t))² - (E f(x_{t+1}) - f(x_t))²`. -/
private noncomputable def stepVar (ε : ℝ) (f : Site d → ℝ) (x : ℕ → Site d) (t : ℕ) : ℝ :=
  ∑ e ∈ unitSteps d, stepProb d ε x t e * (f (x t + e) - f (x t)) ^ 2 -
    (nextMean ε f x t - f (x t)) ^ 2

/-- Almost surely, the conditional expectation of the squared increment of the Dynkin martingale
of `f` is the path functional `stepVar`. -/
private theorem condExp_sq_dynkin_eq_stepVar (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    {ε : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d} (hε : 0 ≤ ε)
    (hεd : ε < 1 / (d : ℝ)) (hX : IsCERW μ ε X) (f : Site d → ℝ) (t : ℕ) :
    μ[fun ω => (dynkin ε f X (t + 1) ω - dynkin ε f X t ω) *
        (dynkin ε f X (t + 1) ω - dynkin ε f X t ω) | pathFiltration hX.measurable t]
      =ᵐ[μ] fun ω => stepVar ε f (fun j => X j ω) t := by
  set h : ((i : Finset.Iic t) → Site d) → Site d → ℝ :=
    fun p z => (f z - nextMean ε f (extendPath p) t) ^ 2 with hh
  have hsq : (fun ω => (dynkin ε f X (t + 1) ω - dynkin ε f X t ω) *
        (dynkin ε f X (t + 1) ω - dynkin ε f X t ω)) =
      fun ω => h (pastPath X t ω) (X (t + 1) ω) := by
    funext ω
    rw [dynkin_succ_sub, nextMean_pastPath, hh]
    ring
  have hint := integrable_path_next hd hε hεd hX t h
  rw [hsq]
  filter_upwards [condExp_path_next hd hε hεd hX t h hint] with ω hω
  rw [hω]
  simp only [hh, ← nextMean_pastPath]
  have hvar := sum_mul_sub_mean_sq (unitSteps d) (fun e => stepProb d ε (fun j => X j ω) t e)
    (fun e => f (X t ω + e)) (sum_stepProb hd ε _ t) (f (X t ω))
  simp only [nextMean] at hvar ⊢
  rw [hvar]
  rfl


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

/-- `Δf(x) = (P - I) f(x)` is the mean of the nearest-neighbour increments of `f` at `x`. -/
private theorem walkOp_sub_self_eq (hd : 1 ≤ d) (f : Site d → ℝ) (x : Site d) :
    walkOp f x - f x = (1 / (2 * d)) * ∑ e ∈ unitSteps d, (f (x + e) - f x) := by
  have h1 := sum_srwStep_mul f x
  have h2 := sum_srwStep hd
  have h3 : ∑ e ∈ unitSteps d, srwStep d e * (f (x + e) - f x) = walkOp f x - f x := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, h2, one_mul]
  rw [← h3, Finset.mul_sum]
  exact Finset.sum_congr rfl fun e he => by rw [srwStep_of_mem he]

/-- The pointwise bracket is the variance of the increments under uniform weights. -/
private theorem gammaBr_self_eq (hd : 1 ≤ d) (f : Site d → ℝ) (x : Site d) :
    gammaBr f f x = (1 / (2 * d)) * ∑ e ∈ unitSteps d, (f (x + e) - f x) ^ 2 -
      ((1 / (2 * d)) * ∑ e ∈ unitSteps d, (f (x + e) - f x)) ^ 2 := by
  rw [gammaBr, walkOp_sub_self_eq hd]
  simp only [sq]

/-- The path functional `stepVar` is the variance of the increments of `f` under the step law. -/
private theorem stepVar_eq (hd : 1 ≤ d) (ε : ℝ) (f : Site d → ℝ) (x : ℕ → Site d) (t : ℕ) :
    stepVar ε f x t = ∑ e ∈ unitSteps d, stepProb d ε x t e * (f (x t + e) - f (x t)) ^ 2 -
      (∑ e ∈ unitSteps d, stepProb d ε x t e * (f (x t + e) - f (x t))) ^ 2 := by
  have h : nextMean ε f x t - f (x t) =
      ∑ e ∈ unitSteps d, stepProb d ε x t e * (f (x t + e) - f (x t)) := by
    simp only [nextMean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_stepProb hd ε x t,
      one_mul]
  rw [stepVar, h]

/-- At a departure that is not the first departure from a nonzero site, the conditional variance
is the pointwise bracket. -/
private theorem stepVar_eq_gammaBr (hd : 1 ≤ d) (ε : ℝ) (f : Site d → ℝ) (x : ℕ → Site d)
    (t : ℕ) (h : ¬(x t ≠ 0 ∧ x t ∉ (Finset.range t).image x)) :
    stepVar ε f x t = gammaBr f f (x t) := by
  rw [stepVar_eq hd, gammaBr_self_eq hd]
  have hp : ∀ e ∈ unitSteps d, stepProb d ε x t e = 1 / (2 * d) := fun e he => by
    rw [stepProb, if_neg h, srwStep_of_mem he]
  have h1 : ∑ e ∈ unitSteps d, stepProb d ε x t e * (f (x t + e) - f (x t)) ^ 2 =
      (1 / (2 * d)) * ∑ e ∈ unitSteps d, (f (x t + e) - f (x t)) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e he => by rw [hp e he]
  have h2 : ∑ e ∈ unitSteps d, stepProb d ε x t e * (f (x t + e) - f (x t)) =
      (1 / (2 * d)) * ∑ e ∈ unitSteps d, (f (x t + e) - f (x t)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e he => by rw [hp e he]
  rw [h1, h2]

/-- At the first departure from a nonzero site `z`, the conditional variance is within
`3 B²` of the pointwise bracket when the increments of `f` at `z` are bounded by `B`. -/
private theorem abs_stepVar_sub_gammaBr_le (hd : 1 ≤ d) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1 / (d : ℝ)) (f : Site d → ℝ) (x : ℕ → Site d) (t : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hinc : ∀ e ∈ unitSteps d, |f (x t + e) - f (x t)| ≤ B) :
    |stepVar ε f x t - gammaBr f f (x t)| ≤ 3 * B ^ 2 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hN : ((unitSteps d).card : ℝ) = 2 * d := by rw [card_unitSteps]; push_cast; ring
  have hNpos : (0 : ℝ) < 2 * d := by positivity
  rw [stepVar_eq hd, gammaBr_self_eq hd]
  have hcon : ∀ e ∈ unitSteps d, |stepProb d ε x t e - 1 / (2 * d)| ≤ ε / 2 := by
    intro e he
    unfold stepProb
    split_ifs with h
    · exact abs_firstStep_sub_le hε0 _ he
    · rw [srwStep_of_mem he, sub_self, abs_zero]
      linarith
  have key := abs_var_sub_le (unitSteps d) hN hNpos (fun e => stepProb d ε x t e)
    (fun e => f (x t + e) - f (x t)) (fun e _ => stepProb_nonneg hε0 hε1 x t e)
    (sum_stepProb hd ε x t) hcon hinc hB (by linarith)
  have hε' : 2 * (d : ℝ) * (ε / 2) ≤ 1 := by
    have := (lt_div_iff₀ hdpos).mp hε1
    nlinarith
  calc _ ≤ 3 * (2 * (d : ℝ)) * (ε / 2) * B ^ 2 := key
    _ ≤ 3 * 1 * B ^ 2 := by
        have h1 : 3 * (2 * (d : ℝ)) * (ε / 2) = 3 * (2 * (d : ℝ) * (ε / 2)) := by ring
        rw [h1]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hε' (by norm_num))
          (sq_nonneg B)
    _ = 3 * B ^ 2 := by ring


/-- The square of `(1 + ρ)^{1-d}` is `(1 + ρ)^{2-2d}`. -/
private theorem one_add_rpow_sq {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ((1 + ρ) ^ (1 - (d : ℝ))) ^ 2 = (1 + ρ) ^ (2 - 2 * (d : ℝ)) := by
  have hbase : 0 ≤ (1 + ρ : ℝ) := by linarith
  rw [← Real.rpow_natCast, ← Real.rpow_mul hbase]
  congr 1
  push_cast
  ring

/-- **The bracket of a Dynkin martingale** (`eq:site-bracket`): almost surely, for every `n`,
`⟨M^f⟩_n` differs from `Σ_x ℓ_n(x) Γ(f, f)(x)` by at most `3 C²` times the sum of
`(1 + |x|)^{2-2d}` over the departure range, when the increments of `f` at `x` are at most
`C (1 + |x|)^{1-d}`. -/
private theorem ae_abs_predBracket_sub_le {Ω : Type*} [MeasurableSpace Ω] {ε : ℝ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d} (hd : 1 ≤ d) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1 / (d : ℝ)) (hX : IsCERW μ ε X) {f : Site d → ℝ} {C : ℝ}
    (hC : ∀ x e, e ∈ unitSteps d → |f (x + e) - f x| ≤ C * (1 + euclidNorm x) ^ (1 - (d : ℝ))) :
    ∀ᵐ ω ∂μ, ∀ n, |predBracket μ (pathFiltration hX.measurable) (dynkin ε f X) (dynkin ε f X) n ω -
        ∑ x ∈ departureRange (fun j => X j ω) n,
          (localTime (fun j => X j ω) n x : ℝ) * gammaBr f f x| ≤
      3 * C ^ 2 * ∑ x ∈ departureRange (fun j => X j ω) n,
        (1 + euclidNorm x) ^ (2 - 2 * (d : ℝ)) := by
  have hCnn : 0 ≤ C := cg_nonneg hd hC
  have hall : ∀ᵐ ω ∂μ, ∀ t, (μ[fun ω => (dynkin ε f X (t + 1) ω - dynkin ε f X t ω) *
        (dynkin ε f X (t + 1) ω - dynkin ε f X t ω) | pathFiltration hX.measurable t]) ω =
      stepVar ε f (fun j => X j ω) t :=
    ae_all_iff.mpr fun t => condExp_sq_dynkin_eq_stepVar hd hε0 hε1 hX f t
  filter_upwards [hall] with ω hω n
  have hpb : predBracket μ (pathFiltration hX.measurable) (dynkin ε f X) (dynkin ε f X) n ω =
      ∑ t ∈ Finset.range n, stepVar ε f (fun j => X j ω) t := by
    simp only [predBracket, Finset.sum_apply]
    exact Finset.sum_congr rfl fun t _ => hω t
  rw [hpb, ← sum_range_eq_sum_localTime (fun j => X j ω) n (gammaBr f f),
    ← Finset.sum_sub_distrib]
  set w : Site d → ℝ := fun z => (1 + euclidNorm z) ^ (2 - 2 * (d : ℝ)) with hw
  have hterm : ∀ t ∈ Finset.range n,
      |stepVar ε f (fun j => X j ω) t - gammaBr f f (X t ω)| ≤
        3 * C ^ 2 * (if X t ω ≠ 0 ∧ X t ω ∉ (Finset.range t).image (fun j => X j ω) then
          w (X t ω) else 0) := by
    intro t _
    by_cases hfresh : X t ω ≠ 0 ∧ X t ω ∉ (Finset.range t).image (fun j => X j ω)
    · rw [if_pos hfresh]
      have hB : 0 ≤ C * (1 + euclidNorm (X t ω)) ^ (1 - (d : ℝ)) :=
        mul_nonneg hCnn (Real.rpow_nonneg (by linarith [euclidNorm_nonneg (X t ω)]) _)
      have h := abs_stepVar_sub_gammaBr_le hd hε0 hε1 f (fun j => X j ω) t hB
        (fun e he => hC (X t ω) e he)
      refine h.trans (le_of_eq ?_)
      rw [mul_pow, one_add_rpow_sq (euclidNorm_nonneg _)]
      ring
    · rw [if_neg hfresh, mul_zero]
      have := stepVar_eq_gammaBr hd ε f (fun j => X j ω) t hfresh
      rw [show (X t ω) = (fun j => X j ω) t from rfl, ← this, sub_self, abs_zero]
  calc |∑ t ∈ Finset.range n, (stepVar ε f (fun j => X j ω) t - gammaBr f f (X t ω))|
      ≤ ∑ t ∈ Finset.range n, |stepVar ε f (fun j => X j ω) t - gammaBr f f (X t ω)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range n, 3 * C ^ 2 *
          (if X t ω ≠ 0 ∧ X t ω ∉ (Finset.range t).image (fun j => X j ω) then
            w (X t ω) else 0) := Finset.sum_le_sum hterm
    _ = 3 * C ^ 2 * ∑ z ∈ departureRange (fun j => X j ω) n, (if z ≠ 0 then w z else 0) := by
        rw [← Finset.mul_sum, sum_fresh_ne_zero_eq_sum_departureRange (fun j => X j ω) n w]
    _ ≤ 3 * C ^ 2 * ∑ z ∈ departureRange (fun j => X j ω) n, w z := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => ?_) (by positivity)
        split_ifs
        · exact le_rfl
        · exact Real.rpow_nonneg (by linarith [euclidNorm_nonneg z]) _


/-! ### The Dynkin martingale of a function with decaying increments -/

/-- **Bounded increments, integrability and adaptedness.** For `f` whose increments at `x` are at
most `C (1 + |x|)^{1-d}`, the Dynkin martingale of `f` is a martingale, starts at zero, is square
integrable, and almost surely has increments at most `2 C`. -/
private theorem dynkin_martingale_facts {Ω : Type*} [MeasurableSpace Ω] {ε : ℝ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d} (hd : 1 ≤ d) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1 / (d : ℝ)) (hX : IsCERW μ ε X) {f : Site d → ℝ} {C : ℝ}
    (hC : ∀ x e, e ∈ unitSteps d → |f (x + e) - f x| ≤ C * (1 + euclidNorm x) ^ (1 - (d : ℝ))) :
    Martingale (dynkin ε f X) (pathFiltration hX.measurable) μ ∧
      (∀ n, MemLp (dynkin ε f X n) 2 μ) ∧ (∀ ω, dynkin ε f X 0 ω = 0) ∧
      ∀ᵐ ω ∂μ, ∀ n, |dynkin ε f X (n + 1) ω - dynkin ε f X n ω| ≤ 2 * C := by
  have hmart := martingale_dynkin hd hε0 hε1 hX f
  have hinc : ∀ᵐ ω ∂μ, ∀ n, |dynkin ε f X (n + 1) ω - dynkin ε f X n ω| ≤ 2 * C := by
    filter_upwards [ae_abs_dynkin_succ_sub_le hd hε0 hε1 hX f] with ω hω n
    have h1 : (1 + euclidNorm (X n ω)) ^ (1 - (d : ℝ)) ≤ 1 :=
      rpow_one_add_le_one (euclidNorm_nonneg _) (by
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        linarith)
    have hCnn := cg_nonneg hd hC
    have h2 := hω n (C * (1 + euclidNorm (X n ω)) ^ (1 - (d : ℝ))) (fun e he => hC _ e he)
    calc _ ≤ 2 * (C * (1 + euclidNorm (X n ω)) ^ (1 - (d : ℝ))) := h2
      _ ≤ 2 * (C * 1) := by
          gcongr
      _ = 2 * C := by ring
  have hbound : ∀ᵐ ω ∂μ, ∀ n, |dynkin ε f X n ω| ≤ 2 * C * n := by
    filter_upwards [hinc] with ω hω n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := hω n
      have h2 : |dynkin ε f X (n + 1) ω| ≤ |dynkin ε f X n ω| +
          |dynkin ε f X (n + 1) ω - dynkin ε f X n ω| := by
        have := abs_add_le (dynkin ε f X n ω) (dynkin ε f X (n + 1) ω - dynkin ε f X n ω)
        rwa [add_sub_cancel] at this
      push_cast
      linarith
  refine ⟨hmart, fun n => ?_, fun ω => dynkin_zero ε f X ω, hinc⟩
  refine MemLp.of_bound
    ((hmart.1 n).mono ((pathFiltration hX.measurable).le n)).aestronglyMeasurable
    (2 * C * n) ?_
  filter_upwards [hbound] with ω hω
  rw [Real.norm_eq_abs]
  exact hω n

/-- The Dynkin martingale of a combination of functions is the combination of the Dynkin
martingales. -/
private theorem dynkin_combo {Ω : Type*} (ε : ℝ) (b : Site d → ℝ) {k : ℕ} (y : Fin k → Site d)
    (s : Fin k → ℝ) (X : ℕ → Ω → Site d) (n : ℕ) (ω : Ω) :
    dynkin ε (combo b y s) X n ω = ∑ i, s i * dynkin ε (fun z => b (z - y i)) X n ω := by
  have hnext : ∀ (x : ℕ → Site d) (j : ℕ), nextMean ε (combo b y s) x j =
      ∑ i, s i * nextMean ε (fun z => b (z - y i)) x j := by
    intro x j
    simp only [nextMean, combo, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun e _ => by ring
  have hswap : ∀ (F : Fin k → ℕ → ℝ) (m : ℕ),
      ∑ x ∈ Finset.range m, ∑ i, s i * F i x = ∑ i, s i * ∑ x ∈ Finset.range m, F i x := by
    intro F m
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  simp only [dynkin, hnext, combo, mul_sub, Finset.sum_sub_distrib]
  rw [hswap (fun i x => nextMean ε (fun z => b (z - y i)) (fun i => X i ω) x) n,
    hswap (fun i x => b (X x ω - y i)) n]

/-- Increments of a combination of translates of a kernel with decaying increments decay like
`(1 + |x|)^{1-d}`. -/
private theorem combo_grad_bound {b : Site d → ℝ} {Cg : ℝ}
    (hg : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (hd : 1 ≤ d) {k : ℕ} (y : Fin k → Site d) (s : Fin k → ℝ) :
    ∃ C : ℝ, ∀ x e, e ∈ unitSteps d →
      |combo b y s (x + e) - combo b y s x| ≤ C * (1 + euclidNorm x) ^ (1 - (d : ℝ)) := by
  have hCg : 0 ≤ Cg := cg_nonneg hd hg
  refine ⟨∑ i, |s i| * (Cg * (1 + euclidNorm (y i)) ^ ((d : ℝ) - 1)), fun x e he => ?_⟩
  have hdiff : combo b y s (x + e) - combo b y s x =
      ∑ i, s i * (b (x - y i + e) - b (x - y i)) := by
    simp only [combo, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_sub_right_comm]
    ring
  rw [hdiff, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have hx0 : 0 ≤ euclidNorm x := euclidNorm_nonneg x
  have hyi : 0 ≤ euclidNorm (y i) := euclidNorm_nonneg _
  have hxy : 0 ≤ euclidNorm (x - y i) := euclidNorm_nonneg _
  have hcmp : (1 + euclidNorm (x - y i)) ^ (1 - (d : ℝ)) ≤
      (1 + euclidNorm (y i)) ^ ((d : ℝ) - 1) * (1 + euclidNorm x) ^ (1 - (d : ℝ)) := by
    have h1 : 1 + euclidNorm x ≤ (1 + euclidNorm (y i)) * (1 + euclidNorm (x - y i)) := by
      have := euclidNorm_sub_le x (y i)
      have h2 : euclidNorm x ≤ euclidNorm (x - y i) + euclidNorm (y i) := by
        have := euclidNorm_add_le (x - y i) (y i)
        rwa [sub_add_cancel] at this
      nlinarith [mul_nonneg hyi hxy]
    have hpos1 : 0 < 1 + euclidNorm (y i) := by linarith
    have hpos2 : 0 < 1 + euclidNorm (x - y i) := by linarith
    have hpos3 : 0 < 1 + euclidNorm x := by linarith
    have hexp : 1 - (d : ℝ) ≤ 0 := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have h3 : (1 + euclidNorm x) / (1 + euclidNorm (y i)) ≤ 1 + euclidNorm (x - y i) := by
      rw [div_le_iff₀ hpos1]
      linarith
    calc (1 + euclidNorm (x - y i)) ^ (1 - (d : ℝ))
        ≤ ((1 + euclidNorm x) / (1 + euclidNorm (y i))) ^ (1 - (d : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h3 hexp
      _ = (1 + euclidNorm (y i)) ^ ((d : ℝ) - 1) * (1 + euclidNorm x) ^ (1 - (d : ℝ)) := by
          rw [Real.div_rpow hpos3.le hpos1.le, div_eq_mul_inv, ← Real.rpow_neg hpos1.le,
            show -(1 - (d : ℝ)) = (d : ℝ) - 1 by ring, mul_comm]
  calc |s i| * |b (x - y i + e) - b (x - y i)|
      ≤ |s i| * (Cg * (1 + euclidNorm (x - y i)) ^ (1 - (d : ℝ))) :=
        mul_le_mul_of_nonneg_left (hg _ e he) (abs_nonneg _)
    _ ≤ |s i| * (Cg * ((1 + euclidNorm (y i)) ^ ((d : ℝ) - 1) *
          (1 + euclidNorm x) ^ (1 - (d : ℝ)))) := by gcongr
    _ = |s i| * (Cg * (1 + euclidNorm (y i)) ^ ((d : ℝ) - 1)) *
          (1 + euclidNorm x) ^ (1 - (d : ℝ)) := by ring

/-- The pointwise bracket of a function with itself is nonnegative. -/
private theorem gammaBr_self_nonneg (hd : 1 ≤ d) (f : Site d → ℝ) (x : Site d) :
    0 ≤ gammaBr f f x := by
  rw [gammaBr_self_eq hd, sub_nonneg]
  have hN : ((unitSteps d).card : ℝ) = 2 * d := by rw [card_unitSteps]; push_cast; ring
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have h := sq_sum_le_card_mul_sum_sq (s := unitSteps d) (f := fun e => f (x + e) - f x)
  rw [hN] at h
  calc ((1 / (2 * (d : ℝ))) * ∑ e ∈ unitSteps d, (f (x + e) - f x)) ^ 2
      = (1 / (2 * (d : ℝ))) ^ 2 * (∑ e ∈ unitSteps d, (f (x + e) - f x)) ^ 2 := mul_pow _ _ _
    _ ≤ (1 / (2 * (d : ℝ))) ^ 2 * (2 * d * ∑ e ∈ unitSteps d, (f (x + e) - f x) ^ 2) := by
        gcongr
    _ = 1 / (2 * (d : ℝ)) * ∑ e ∈ unitSteps d, (f (x + e) - f x) ^ 2 := by
        field_simp

/-- The pointwise bracket of a function with itself is at most the mean square increment. -/
private theorem gammaBr_self_le (hd : 1 ≤ d) (f : Site d → ℝ) {B : ℝ} (x : Site d)
    (hinc : ∀ e ∈ unitSteps d, |f (x + e) - f x| ≤ B) : gammaBr f f x ≤ B ^ 2 := by
  rw [gammaBr_self_eq hd]
  have hN : ((unitSteps d).card : ℝ) = 2 * d := by rw [card_unitSteps]; push_cast; ring
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hsum : ∑ e ∈ unitSteps d, (f (x + e) - f x) ^ 2 ≤ 2 * d * B ^ 2 := by
    calc ∑ e ∈ unitSteps d, (f (x + e) - f x) ^ 2 ≤ ∑ _e ∈ unitSteps d, B ^ 2 := by
          refine Finset.sum_le_sum fun e he => ?_
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hinc e he) 2
      _ = 2 * d * B ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul, hN]
  have hsq : 0 ≤ ((1 / (2 * (d : ℝ))) * ∑ e ∈ unitSteps d, (f (x + e) - f x)) ^ 2 := sq_nonneg _
  calc 1 / (2 * (d : ℝ)) * ∑ e ∈ unitSteps d, (f (x + e) - f x) ^ 2 -
        ((1 / (2 * (d : ℝ))) * ∑ e ∈ unitSteps d, (f (x + e) - f x)) ^ 2
      ≤ 1 / (2 * (d : ℝ)) * ∑ e ∈ unitSteps d, (f (x + e) - f x) ^ 2 := by linarith
    _ ≤ 1 / (2 * (d : ℝ)) * (2 * d * B ^ 2) := by gcongr
    _ = B ^ 2 := by field_simp


/-! ### The bracket against the local-time profile -/

/-- The shape theorem, in the form used for the brackets: almost surely the departure range is
eventually inside every slightly larger ball, and the local times are uniformly within `η r_n` of
the profile `2 d ε (r_n - |x|)_+`. -/
private theorem ae_shape_consequences (hshape : limit_shape.{u}) (hd : 2 ≤ d) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1 / (d : ℝ)) {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) :
    ∀ᵐ ω ∂μ, (∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
        ∀ x ∈ departureRange (fun j => X j ω) n, euclidNorm x < (1 + η) * radius d ε n) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site d,
        |(localTime (fun j => X j ω) n x : ℝ) -
            2 * d * ε * max (radius d ε n - euclidNorm x) 0| ≤ η * radius d ε n) := by
  filter_upwards [hshape hd hε0 hε1 μ X hX] with ω h
  exact ⟨fun η h0 h1 => (h.1 η h0 h1).mono fun n hn x hx => hn.2 (by exact_mod_cast hx),
    h.2.1⟩


/-- `d ≥ 3`: the normalized bracket of a path converges, given a bounded error against the
local-time sum. -/
private theorem tendsto_bracket_high (hd : 2 ≤ d) (hd2 : d ≠ 2) {ε : ℝ} (hε0 : 0 < ε)
    (Y : ℕ → Site d) (P : ℕ → ℝ) (Γ : Site d → ℝ) (hΓ : Summable Γ) (M : ℝ)
    (hB : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site d,
      |(localTime Y n x : ℝ) - 2 * d * ε * max (radius d ε n - euclidNorm x) 0| ≤
        η * radius d ε n)
    (hP : ∀ n, |P n - ∑ x ∈ departureRange Y n, (localTime Y n x : ℝ) * Γ x| ≤ M) :
    Tendsto (fun n => P n / sigmaN d ε n ^ 2) atTop (𝓝 (2 * d * ε * ∑' x, Γ x)) := by
  have hr := radius_tendsto hd hε0
  have hE := tendsto_ell_sum_high Y (radius d ε) hr hB Γ hΓ
  have herr : Tendsto (fun n => (P n - ∑ x ∈ departureRange Y n,
      (localTime Y n x : ℝ) * Γ x) / radius d ε n) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => M / radius d ε n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hr
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [hr.eventually_gt_atTop 0] with n hn
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hn]
    exact div_le_div_of_nonneg_right (hP n) hn.le
  have hsum := hE.add herr
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [scale_sigmaN_sq hd hε0, hr.eventually_gt_atTop 0] with n hn hpos
  rw [hn, if_neg hd2]
  field_simp
  ring

/-- `d = 2`: the normalized bracket of a path converges, given an error of logarithmic order
against the local-time sum. -/
private theorem tendsto_bracket_planar {ε : ℝ} (hε0 : 0 < ε) (Y : ℕ → Site 2) (P : ℕ → ℝ)
    (Γ : Site 2 → ℝ) (C₁ K : ℝ) (hΓ : ∀ x, |Γ x| ≤ C₁ * (1 + euclidNorm x) ^ (-2 : ℝ))
    (c : ℝ) (hT : ∃ C : ℝ, ∀ ρ : ℝ, 2 ≤ ρ →
      |∑ x ∈ ballFinset 2 ρ, (ρ - euclidNorm x) * Γ x - c * ρ * Real.log ρ| ≤ C * ρ)
    (hA : ∀ᶠ n : ℕ in atTop, ∀ x ∈ departureRange Y n, euclidNorm x ≤ 2 * radius 2 ε n)
    (hB : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site 2,
      |(localTime Y n x : ℝ) - 4 * ε * max (radius 2 ε n - euclidNorm x) 0| ≤
        η * radius 2 ε n)
    (hP : ∀ n, |P n - ∑ x ∈ departureRange Y n, (localTime Y n x : ℝ) * Γ x| ≤
      K * ∑ x ∈ departureRange Y n, (1 + euclidNorm x) ^ (-2 : ℝ)) :
    Tendsto (fun n => P n / sigmaN 2 ε n ^ 2) atTop (𝓝 (4 * ε * c)) := by
  have hr := radius_tendsto (le_refl 2) hε0
  have hE := tendsto_ell_sum_planar Y (radius 2 ε) hr hA hB Γ C₁ hΓ c hT
  obtain ⟨CL, hCLpos, hCL⟩ := CERW.Generic.Lattice.sum_ballFinset_rpow_neg_le_log (d := 2)
    (by norm_num)
  have hr2 : ∀ᶠ n : ℕ in atTop, 2 ≤ radius 2 ε n := hr.eventually_ge_atTop 2
  have herr : Tendsto (fun n => (P n - ∑ x ∈ departureRange Y n,
      (localTime Y n x : ℝ) * Γ x) / (radius 2 ε n * Real.log (radius 2 ε n))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => (3 * |K| * CL) / radius 2 ε n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hr
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [hA, hr2] with n hAn hn
    have hlog : 0 < Real.log (radius 2 ε n) :=
      Real.log_pos (by linarith)
    have hrpos : 0 < radius 2 ε n := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hrpos hlog)]
    have hW : ∑ x ∈ departureRange Y n, (1 + euclidNorm x) ^ (-2 : ℝ) ≤
        CL * Real.log (2 * radius 2 ε n + 2) := by
      calc ∑ x ∈ departureRange Y n, (1 + euclidNorm x) ^ (-2 : ℝ)
          ≤ ∑ x ∈ ballFinset 2 (2 * radius 2 ε n), (1 + euclidNorm x) ^ (-2 : ℝ) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) fun x _ _ =>
              Real.rpow_nonneg (by linarith [euclidNorm_nonneg x]) _
            exact mem_ballFinset_iff.mpr (hAn x hx)
        _ ≤ CL * Real.log (2 * radius 2 ε n + 2) := by
            have := hCL (2 * radius 2 ε n) (by linarith)
            simpa using this
    have hlog3 : Real.log (2 * radius 2 ε n + 2) ≤ 3 * Real.log (radius 2 ε n) := by
      have h1 : 2 * radius 2 ε n + 2 ≤ 2 * radius 2 ε n ^ 2 := by nlinarith
      calc Real.log (2 * radius 2 ε n + 2) ≤ Real.log (2 * radius 2 ε n ^ 2) :=
            Real.log_le_log (by linarith) h1
        _ = Real.log 2 + 2 * Real.log (radius 2 ε n) := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
            push_cast
            ring
        _ ≤ 3 * Real.log (radius 2 ε n) := by
            have : Real.log 2 ≤ Real.log (radius 2 ε n) := Real.log_le_log (by norm_num) hn
            linarith
    have hKW : K * ∑ x ∈ departureRange Y n, (1 + euclidNorm x) ^ (-2 : ℝ) ≤
        |K| * (CL * (3 * Real.log (radius 2 ε n))) := by
      calc K * ∑ x ∈ departureRange Y n, (1 + euclidNorm x) ^ (-2 : ℝ)
          ≤ |K| * ∑ x ∈ departureRange Y n, (1 + euclidNorm x) ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_right (le_abs_self K)
              (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (by linarith [euclidNorm_nonneg x]) _)
        _ ≤ |K| * (CL * (3 * Real.log (radius 2 ε n))) := by
            refine mul_le_mul_of_nonneg_left (hW.trans ?_) (abs_nonneg K)
            exact mul_le_mul_of_nonneg_left hlog3 hCLpos.le
    have hnum := (hP n).trans hKW
    calc |P n - ∑ x ∈ departureRange Y n, (localTime Y n x : ℝ) * Γ x| /
          (radius 2 ε n * Real.log (radius 2 ε n))
        ≤ |K| * (CL * (3 * Real.log (radius 2 ε n))) /
          (radius 2 ε n * Real.log (radius 2 ε n)) :=
          div_le_div_of_nonneg_right hnum (mul_pos hrpos hlog).le
      _ = 3 * |K| * CL / radius 2 ε n := by
          field_simp
  have hsum := hE.add herr
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [scale_sigmaN_sq (le_refl 2) hε0, hr.eventually_gt_atTop 0] with n hn hpos
  rw [hn, if_pos rfl]
  ring


/-- For `d ≥ 3` the weight `(1 + |z|)^{2-2d}` is summable over the lattice. -/
private theorem summable_one_add_rpow_two_sub_two_mul (hd : 3 ≤ d) :
    Summable fun z : Site d => (1 + euclidNorm z) ^ (2 - 2 * (d : ℝ)) := by
  have h := summable_one_add_euclidNorm_rpow d (p := 2 * (d : ℝ) - 2) (by
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith)
  refine h.congr fun z => ?_
  rw [show -(2 * (d : ℝ) - 2) = 2 - 2 * (d : ℝ) by ring]

/-- **The normalized bracket converges almost surely** (`eq:site-bracket` with Steps 2 and 3): for
a combination `f` of translates of the lattice kernel, `⟨M^f⟩_n / σ_n²` converges to the quadratic
form of the limiting covariance. -/
private theorem ae_bracket_tendsto (hshape : limit_shape.{u}) (hd : 2 ≤ d) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1 / (d : ℝ)) {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) {k : ℕ}
    (y : Fin k → Site d) (s : Fin k → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => predBracket μ (pathFiltration hX.measurable)
        (dynkin ε (combo (latticeKernel d) y s) X) (dynkin ε (combo (latticeKernel d) y s) X)
          n ω / sigmaN d ε n ^ 2) atTop
      (𝓝 (∑ i, ∑ j, s i * s j * covN d ε (y i) (y j))) := by
  obtain ⟨h, hK⟩ := exists_kernelFacts_latticeKernel hd
  obtain ⟨Cg, hg⟩ := hK.gradBound
  obtain ⟨C, hC⟩ := combo_grad_bound hg (by omega) y s
  have hbr := ae_abs_predBracket_sub_le (by omega) hε0.le hε1 hX hC
  have hsh := ae_shape_consequences hshape hd hε0 hε1 μ hX
  have hΓle : ∀ x, gammaBr (combo (latticeKernel d) y s) (combo (latticeKernel d) y s) x ≤
      C ^ 2 * (1 + euclidNorm x) ^ (2 - 2 * (d : ℝ)) := by
    intro x
    have hB : 0 ≤ C * (1 + euclidNorm x) ^ (1 - (d : ℝ)) :=
      mul_nonneg (cg_nonneg (by omega) hC)
        (Real.rpow_nonneg (by linarith [euclidNorm_nonneg x]) _)
    have := gammaBr_self_le (by omega) (combo (latticeKernel d) y s) x (fun e he => hC x e he)
    rw [mul_pow, one_add_rpow_sq (euclidNorm_nonneg _)] at this
    exact this
  filter_upwards [hbr, hsh] with ω hbrω hshω
  obtain ⟨hA, hB⟩ := hshω
  rcases Nat.lt_or_ge d 3 with h3 | h3
  · obtain rfl : d = 2 := by omega
    obtain ⟨CT, hT⟩ := gamma_ball_sum_planar y s
    have hcast : (2 - 2 * ((2 : ℕ) : ℝ)) = -2 := by norm_num
    have hlim := tendsto_bracket_planar hε0 (fun j => X j ω)
      (fun n => predBracket μ (pathFiltration hX.measurable)
        (dynkin ε (combo (latticeKernel 2) y s) X) (dynkin ε (combo (latticeKernel 2) y s) X) n ω)
      (gammaBr (combo (latticeKernel 2) y s) (combo (latticeKernel 2) y s)) (C ^ 2) (3 * C ^ 2)
      (fun x => by
        rw [abs_of_nonneg (gammaBr_self_nonneg (by norm_num) _ x)]
        have := hΓle x
        rwa [hcast] at this)
      (4 / Real.pi * (∑ i, s i) ^ 2) ⟨CT, hT⟩
      ((hA (1 / 2) (by norm_num) (by norm_num)).mp
        ((radius_tendsto (le_refl 2) hε0).eventually_ge_atTop 0 |>.mono fun n hn hAn x hx =>
          (hAn x hx).le.trans (by linarith)))
      (fun η hη => (hB η hη).mono fun n hn x => by
        have := hn x
        rwa [show (2 : ℝ) * ((2 : ℕ) : ℝ) = 4 by norm_num] at this)
      (fun n => by
        have := hbrω n
        rwa [hcast] at this)
    convert hlim using 2
    simp only [covN, if_true]
    have h1 : ∑ i, ∑ j, s i * s j * (16 * ε / Real.pi) =
        (∑ i, s i) * (∑ j, s j) * (16 * ε / Real.pi) := by
      rw [Finset.sum_mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
    rw [h1]
    ring
  · have hd2 : d ≠ 2 := by omega
    obtain ⟨hsum, htsum⟩ := gamma_tsum_high h3 y s
    have hw := summable_one_add_rpow_two_sub_two_mul h3
    have hlim := tendsto_bracket_high hd hd2 hε0 (fun j => X j ω)
      (fun n => predBracket μ (pathFiltration hX.measurable)
        (dynkin ε (combo (latticeKernel d) y s) X) (dynkin ε (combo (latticeKernel d) y s) X) n ω)
      (gammaBr (combo (latticeKernel d) y s) (combo (latticeKernel d) y s)) hsum
      (3 * C ^ 2 * ∑' z : Site d, (1 + euclidNorm z) ^ (2 - 2 * (d : ℝ))) hB
      (fun n => by
        refine (hbrω n).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        exact hw.sum_le_tsum _ fun z _ => Real.rpow_nonneg (by linarith [euclidNorm_nonneg z]) _)
    convert hlim using 2
    rw [htsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [covN, if_neg hd2]
    ring


/-! ### The potential term -/

/-- Deterministic bookkeeping for the potential term at one time: the decomposition
`ℓ - P + M = (ℓ - U + M) + (U - P - Q/(ω r^d)) + Q/(ω r^d)`, with `Q = 2ε Σ - n + X²` bounded
through the moment deviation `(Σ - n/(2ε))/r^{(d+3)/2}` and `|X| ≤ 2 r`. -/
private theorem potential_term_bound (d : ℕ) (hd : 2 ≤ d) {ε ωd r : ℝ} (hε : 0 < ε)
    (hωd : 0 < ωd) (hr : 1 ≤ r) (ℓ U Mv P Q Sig nn Xn a b s₁ : ℝ)
    (hA : |ℓ - U + Mv| ≤ a) (hB : |U - P - Q / (ωd * r ^ d)| ≤ b)
    (hQ : Q = 2 * ε * Sig - nn + Xn ^ 2)
    (hS : |(Sig - nn / (2 * ε)) / r ^ (((d : ℝ) + 3) / 2)| ≤ s₁) (hX : |Xn| ≤ 2 * r) :
    |ℓ - P + Mv| ≤ a + b + 2 * ε / ωd * s₁ * r ^ (((3 : ℝ) - d) / 2) + 4 / ωd := by
  have hr0 : 0 < r := by linarith
  have hrd : 0 < r ^ d := pow_pos hr0 d
  have hpow : r ^ (((d : ℝ) + 3) / 2) = r ^ (((3 : ℝ) - d) / 2) * r ^ d := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr0]
    congr 1
    ring
  have hpos1 : 0 < r ^ (((3 : ℝ) - d) / 2) := Real.rpow_pos_of_pos hr0 _
  have hpos2 : 0 < r ^ (((d : ℝ) + 3) / 2) := Real.rpow_pos_of_pos hr0 _
  set Sv := (Sig - nn / (2 * ε)) / r ^ (((d : ℝ) + 3) / 2) with hSv
  have hQ' : Q = 2 * ε * (Sv * r ^ (((d : ℝ) + 3) / 2)) + Xn ^ 2 := by
    rw [hSv, div_mul_cancel₀ _ hpos2.ne', hQ]
    field_simp
  have h1 : ℓ - P + Mv = (ℓ - U + Mv) + (U - P - Q / (ωd * r ^ d)) + Q / (ωd * r ^ d) := by
    ring
  have hXsq : Xn ^ 2 ≤ 4 * r ^ 2 := by
    have := sq_le_sq' (by linarith [abs_nonneg Xn, neg_abs_le Xn]) (abs_le.mp hX).2
    nlinarith [sq_abs Xn, abs_nonneg Xn, this]
  have hr2 : r ^ 2 ≤ r ^ d := pow_le_pow_right₀ hr hd
  have hQbound : |Q / (ωd * r ^ d)| ≤ 2 * ε / ωd * s₁ * r ^ (((3 : ℝ) - d) / 2) + 4 / ωd := by
    have hden : 0 < ωd * r ^ d := mul_pos hωd hrd
    rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
    have h2 : |Q| ≤ 2 * ε * s₁ * (r ^ (((3 : ℝ) - d) / 2) * r ^ d) + 4 * r ^ d := by
      rw [hQ']
      calc |2 * ε * (Sv * r ^ (((d : ℝ) + 3) / 2)) + Xn ^ 2|
          ≤ |2 * ε * (Sv * r ^ (((d : ℝ) + 3) / 2))| + |Xn ^ 2| := abs_add_le _ _
        _ ≤ 2 * ε * s₁ * (r ^ (((3 : ℝ) - d) / 2) * r ^ d) + 4 * r ^ d := by
            have h3 : |2 * ε * (Sv * r ^ (((d : ℝ) + 3) / 2))| ≤
                2 * ε * s₁ * (r ^ (((3 : ℝ) - d) / 2) * r ^ d) := by
              rw [abs_mul (2 * ε), abs_of_pos (by positivity : (0 : ℝ) < 2 * ε), abs_mul Sv,
                abs_of_pos hpos2, ← hpow]
              calc 2 * ε * (|Sv| * r ^ (((d : ℝ) + 3) / 2))
                  ≤ 2 * ε * (s₁ * r ^ (((d : ℝ) + 3) / 2)) := by
                    gcongr
                _ = 2 * ε * s₁ * r ^ (((d : ℝ) + 3) / 2) := by ring
            have h4 : |Xn ^ 2| ≤ 4 * r ^ d := by
              rw [abs_of_nonneg (sq_nonneg _)]
              linarith
            linarith
    calc |Q| ≤ 2 * ε * s₁ * (r ^ (((3 : ℝ) - d) / 2) * r ^ d) + 4 * r ^ d := h2
      _ = (2 * ε / ωd * s₁ * r ^ (((3 : ℝ) - d) / 2) + 4 / ωd) * (ωd * r ^ d) := by
          field_simp
  rw [h1]
  calc |(ℓ - U + Mv) + (U - P - Q / (ωd * r ^ d)) + Q / (ωd * r ^ d)|
      ≤ |(ℓ - U + Mv) + (U - P - Q / (ωd * r ^ d))| + |Q / (ωd * r ^ d)| := abs_add_le _ _
    _ ≤ (|ℓ - U + Mv| + |U - P - Q / (ωd * r ^ d)|) + |Q / (ωd * r ^ d)| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ a + b + (2 * ε / ωd * s₁ * r ^ (((3 : ℝ) - d) / 2) + 4 / ωd) := by
        linarith
    _ = a + b + 2 * ε / ωd * s₁ * r ^ (((3 : ℝ) - d) / 2) + 4 / ωd := by ring


/-- Almost surely, eventually the walk at time `n` is within `2 r_n` of the origin. -/
private theorem ae_walk_le (hfluct : fluctuation_rates.{u}) (hd : 2 ≤ d) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1 / (d : ℝ)) {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, euclidNorm (X n ω) ≤ 2 * radius d ε n := by
  obtain ⟨Cf, hCf, -, hae⟩ := hfluct hd ε hε0 hε1 1 one_pos
  have hr := radius_tendsto hd hε0
  have hsmall : ∀ᶠ n : ℕ in atTop, Cf * (if d = 2 then Real.sqrt (radius d ε n) *
        Real.log n ^ ((5 : ℝ) / 2) else Real.log n ^ ((d : ℝ) + 1)) ≤ radius d ε n := by
    by_cases hd2 : d = 2
    · have h := (scale_log_rpow_div_radius_rpow hd hε0 ((5 : ℝ) / 2) (c := 1 / 2)
        (by norm_num)).const_mul Cf
      rw [mul_zero] at h
      filter_upwards [h.eventually (gt_mem_nhds one_pos), hr.eventually_gt_atTop 0,
        Filter.eventually_ge_atTop 1] with n hn hpos hn1
      rw [if_pos hd2]
      have hlog : Real.log n ^ ((5 : ℝ) / 2) ≤ Real.log (n + 2) ^ ((5 : ℝ) / 2) :=
        Real.rpow_le_rpow (Real.log_nonneg (by exact_mod_cast hn1))
          (Real.log_le_log (by exact_mod_cast hn1) (by linarith)) (by norm_num)
      have hsq : 0 < radius d ε n ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hpos _
      rw [← Real.sqrt_eq_rpow] at hsq hn
      have h1 : Cf * Real.log (n + 2) ^ ((5 : ℝ) / 2) < Real.sqrt (radius d ε n) := by
        have := (mul_div_assoc Cf _ _).symm ▸ hn
        rwa [div_lt_one hsq] at this
      have hsqr : Real.sqrt (radius d ε n) * Real.sqrt (radius d ε n) = radius d ε n :=
        Real.mul_self_sqrt hpos.le
      calc Cf * (Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2))
          = Real.sqrt (radius d ε n) * (Cf * Real.log n ^ ((5 : ℝ) / 2)) := by ring
        _ ≤ Real.sqrt (radius d ε n) * Real.sqrt (radius d ε n) := by
            refine mul_le_mul_of_nonneg_left ?_ hsq.le
            calc Cf * Real.log n ^ ((5 : ℝ) / 2) ≤ Cf * Real.log (n + 2) ^ ((5 : ℝ) / 2) :=
                  mul_le_mul_of_nonneg_left hlog hCf.le
              _ ≤ _ := h1.le
        _ = radius d ε n := hsqr
    · have h := (scale_log_rpow_div_radius_rpow hd hε0 ((d : ℝ) + 1) (c := 1)
        (by norm_num)).const_mul Cf
      rw [mul_zero] at h
      filter_upwards [h.eventually (gt_mem_nhds one_pos), hr.eventually_gt_atTop 0,
        Filter.eventually_ge_atTop 1] with n hn hpos hn1
      rw [if_neg hd2]
      have hlog : Real.log n ^ ((d : ℝ) + 1) ≤ Real.log (n + 2) ^ ((d : ℝ) + 1) :=
        Real.rpow_le_rpow (Real.log_nonneg (by exact_mod_cast hn1))
          (Real.log_le_log (by exact_mod_cast hn1) (by linarith)) (by positivity)
      rw [Real.rpow_one] at hn
      have h1 : Cf * Real.log (n + 2) ^ ((d : ℝ) + 1) < radius d ε n := by
        have := (mul_div_assoc Cf _ _).symm ▸ hn
        rwa [div_lt_one hpos] at this
      calc Cf * Real.log n ^ ((d : ℝ) + 1) ≤ Cf * Real.log (n + 2) ^ ((d : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hlog hCf.le
        _ ≤ radius d ε n := h1.le
  filter_upwards [hae μ X hX] with ω hω
  filter_upwards [hω, hsmall, hr.eventually_gt_atTop 0] with n hn hs hpos
  have h1 := hn.1
  have h2 : euclidNorm (X n ω) ≤ maxRadius (fun j => X j ω) n :=
    euclidNorm_le_maxRadius (fun j => X j ω) le_rfl
  by_cases hd2 : d = 2
  · rw [if_pos hd2] at h1 hs
    have h3 : maxRadius (fun j => X j ω) n - radius d ε n ≤
        Cf * Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2) := h1.2
    rw [← mul_assoc] at hs
    linarith
  · rw [if_neg hd2] at h1 hs
    have h3 : maxRadius (fun j => X j ω) n - radius d ε n ≤
        Cf * Real.log n ^ ((d : ℝ) + 1) := h1.2
    linarith


/-- **The potential term is negligible** (Step 5): almost surely, for large `n`,
`|ℓ_n(y) - 2dε(r_n - |y|) + 𝓜^y_n|` is at most a constant times `errScale`. -/
private theorem ae_potential_term_le (hfluct : fluctuation_rates.{u})
    (hcenter : fixed_site_centering.{u}) (hmom : moment_fluctuations.{u})
    (hCLT : MartingaleCLT.{u}) (hLIL : StoutLIL.{u}) (hd : 2 ≤ d) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1 / (d : ℝ)) {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) (y : Site d) :
    ∃ Ct : ℝ, ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
      |(localTime (fun j => X j ω) n y : ℝ) - 2 * d * ε * (radius d ε n - euclidNorm y) +
        dynkin ε (fun z => latticeKernel d (z - y)) X n ω| ≤ Ct * errScale d ε n := by
  obtain ⟨h, hK⟩ := exists_kernelFacts_latticeKernel hd
  obtain ⟨CP, hCP0, hP⟩ := exists_abs_localTime_sub_potential_add_dynkin_le.{u} hd hK
  obtain ⟨Cc, hCc, hc⟩ := hcenter hd ε hε0 hε1 y
  have hdpos : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hε2 : ε ≤ 1 := by
    have : ε * d < 1 := by
      have := (lt_div_iff₀ (by linarith : (0 : ℝ) < d)).mp hε1
      exact this
    nlinarith
  have hcen : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
      |potential d ε (cellSet (fun j => X j ω) n) (toSpace y) -
          2 * d * ε * (radius d ε n - euclidNorm y) -
          quadraticMart ε (fun j => X j ω) n / (unitBallVolume d * radius d ε n ^ d)| ≤
        Cc * (if d = 2 then Real.log n ^ 3 else 1) := hc μ X hX
  set v₁ : ℝ := 2 * d * unitBallVolume d / (ε * ((d : ℝ) + 2) * ((d : ℝ) + 3)) with hv₁
  have hSlil : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
      |(∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x - n / (2 * ε)) /
          radius d ε n ^ (((d : ℝ) + 3) / 2)| ≤
        (Real.sqrt v₁ + 1) * Real.sqrt (2 * Real.log (Real.log n)) := by
    filter_upwards [(hmom hd hCLT hLIL ε hε0 hε1 μ X hX).2.2] with ω hω
    have h1 := (hω 1 one_pos 1 (Or.inl rfl)).1
    have h2 := (hω 1 one_pos (-1) (Or.inr rfl)).1
    filter_upwards [h1, h2] with n hn1 hn2
    have hn1' : 1 * ((∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x - n / (2 * ε)) /
          radius d ε n ^ (((d : ℝ) + 3) / 2)) ≤
        (Real.sqrt v₁ + 1) * Real.sqrt (2 * Real.log (Real.log n)) := hn1
    have hn2' : -1 * ((∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x - n / (2 * ε)) /
          radius d ε n ^ (((d : ℝ) + 3) / 2)) ≤
        (Real.sqrt v₁ + 1) * Real.sqrt (2 * Real.log (Real.log n)) := hn2
    rw [abs_le]
    constructor <;> linarith
  have hwalk := ae_walk_le hfluct hd hε0 hε1 μ hX
  have hpath := ae_euclidNorm_le (by omega : 1 ≤ d) hε0.le hε1 hX
  have h0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
    rw [ae_iff]
    exact hX.start
  have hr := radius_tendsto hd hε0
  have hωd := unitBallVolume_pos d
  refine ⟨CP + Cc + 2 * ε / unitBallVolume d * (Real.sqrt v₁ + 1) * Real.sqrt 2 +
    4 / unitBallVolume d, ?_⟩
  filter_upwards [h0, hpath, hcen, hSlil, hwalk] with ω h0ω hpathω hcenω hSω hwω
  filter_upwards [hcenω, hSω, hwω, hr.eventually_ge_atTop 1,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (euclidNorm y),
    Filter.eventually_ge_atTop 16] with n hc1 hS1 hw1 hr1 hyn hn16
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hy3 : euclidNorm y ≤ 3 * n := by linarith
  have hPn := hP ε hε0.le hε2 X ω h0ω hpathω n hn1 y hy3
  have hL1 : 1 ≤ Real.log ((n : ℝ) + 2) := one_le_log_add_two (by omega)
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hkey := potential_term_bound d hd hε0 hωd hr1
    (localTime (fun j => X j ω) n y : ℝ) (potential d ε (cellSet (fun j => X j ω) n) (toSpace y))
    (dynkin ε (fun z => latticeKernel d (z - y)) X n ω) (2 * d * ε * (radius d ε n - euclidNorm y))
    (quadraticMart ε (fun j => X j ω) n) (∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x)
    n (euclidNorm (X n ω)) (CP * Real.log ((n : ℝ) + 2))
    (Cc * (if d = 2 then Real.log n ^ 3 else 1))
    ((Real.sqrt v₁ + 1) * Real.sqrt (2 * Real.log (Real.log n))) hPn hc1 rfl hS1
    (by rw [abs_of_nonneg (euclidNorm_nonneg _)]; exact hw1)
  set L := Real.log ((n : ℝ) + 2) with hL
  set A := L ^ 3 with hA
  set B := radius d ε n ^ (((3 : ℝ) - d) / 2) * Real.sqrt (Real.log (Real.log n) + 1) with hB
  have hA1 : 1 ≤ A := one_le_pow₀ hL1
  have hLA : L ≤ A := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.sqrt_nonneg _)
  have hK₃ : 0 ≤ 2 * ε / unitBallVolume d * (Real.sqrt v₁ + 1) * Real.sqrt 2 := by positivity
  have hb : Cc * (if d = 2 then Real.log n ^ 3 else 1) ≤ Cc * A := by
    refine mul_le_mul_of_nonneg_left ?_ hCc.le
    split_ifs
    · exact pow_le_pow_left₀ hlogn (Real.log_le_log (by exact_mod_cast (by omega : 0 < n))
        (by linarith)) 3
    · exact hA1
  have hs : 2 * ε / unitBallVolume d *
        ((Real.sqrt v₁ + 1) * Real.sqrt (2 * Real.log (Real.log n))) *
        radius d ε n ^ (((3 : ℝ) - d) / 2) ≤
      2 * ε / unitBallVolume d * (Real.sqrt v₁ + 1) * Real.sqrt 2 * B := by
    have h1 : Real.sqrt (2 * Real.log (Real.log n)) ≤
        Real.sqrt 2 * Real.sqrt (Real.log (Real.log n) + 1) := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (by linarith)
    have hpos : 0 ≤ 2 * ε / unitBallVolume d * (Real.sqrt v₁ + 1) := by positivity
    have hrp : 0 ≤ radius d ε n ^ (((3 : ℝ) - d) / 2) := Real.rpow_nonneg (by linarith) _
    calc 2 * ε / unitBallVolume d * ((Real.sqrt v₁ + 1) * Real.sqrt (2 * Real.log (Real.log n))) *
          radius d ε n ^ (((3 : ℝ) - d) / 2)
        = (2 * ε / unitBallVolume d * (Real.sqrt v₁ + 1)) *
            Real.sqrt (2 * Real.log (Real.log n)) * radius d ε n ^ (((3 : ℝ) - d) / 2) := by
          ring
      _ ≤ (2 * ε / unitBallVolume d * (Real.sqrt v₁ + 1)) *
            (Real.sqrt 2 * Real.sqrt (Real.log (Real.log n) + 1)) *
            radius d ε n ^ (((3 : ℝ) - d) / 2) := by
          gcongr
      _ = 2 * ε / unitBallVolume d * (Real.sqrt v₁ + 1) * Real.sqrt 2 * B := by
          rw [hB]
          ring
  have hinv : 4 / unitBallVolume d ≤ 4 / unitBallVolume d * A := by
    have : 0 ≤ 4 / unitBallVolume d := by positivity
    nlinarith
  have hCPA : CP * L ≤ CP * A := mul_le_mul_of_nonneg_left hLA hCP0
  have hfinal : |(localTime (fun j => X j ω) n y : ℝ) - 2 * d * ε * (radius d ε n - euclidNorm y) +
      dynkin ε (fun z => latticeKernel d (z - y)) X n ω| ≤
      (CP + Cc + 2 * ε / unitBallVolume d * (Real.sqrt v₁ + 1) * Real.sqrt 2 +
        4 / unitBallVolume d) * (A + B) := by
    have h5 : (CP + Cc + 2 * ε / unitBallVolume d * (Real.sqrt v₁ + 1) * Real.sqrt 2 +
        4 / unitBallVolume d) * (A + B) =
        CP * A + Cc * A + 4 / unitBallVolume d * A +
        (CP + Cc + 4 / unitBallVolume d) * B +
        2 * ε / unitBallVolume d * (Real.sqrt v₁ + 1) * Real.sqrt 2 * (A + B) := by ring
    have h6 : 0 ≤ (CP + Cc + 4 / unitBallVolume d) * B := by positivity
    have h7 : 2 * ε / unitBallVolume d * (Real.sqrt v₁ + 1) * Real.sqrt 2 * B ≤
        2 * ε / unitBallVolume d * (Real.sqrt v₁ + 1) * Real.sqrt 2 * (A + B) :=
      mul_le_mul_of_nonneg_left (by linarith) hK₃
    linarith
  exact hfinal


/-! ### The limiting covariance -/

/-- The simple random walk Green function is symmetric. -/
private theorem srwGreenInf_neg (x : Site d) : srwGreenInf d (-x) = srwGreenInf d x := by
  simp only [srwGreenInf, srwHeat_neg]

/-- The limiting covariance is symmetric. -/
private theorem covN_comm (ε : ℝ) (a b : Site d) : covN d ε a b = covN d ε b a := by
  by_cases hd2 : d = 2
  · simp only [covN, if_pos hd2]
  · simp only [covN, if_neg hd2]
    have hab : srwGreenInf d (a - b) = srwGreenInf d (b - a) := by
      rw [← neg_sub a b, srwGreenInf_neg]
    have hif : (if a = b then (1 : ℝ) else 0) = if b = a then 1 else 0 := by
      by_cases h : a = b
      · subst h
        simp
      · simp [h, Ne.symm h]
    rw [hab, hif]

/-- The Green function at the origin is at least one. -/
private theorem one_le_srwGreenInf_zero (hd : 3 ≤ d) : 1 ≤ srwGreenInf d (0 : Site d) := by
  have hsum := summable_srwHeat hd (0 : Site d)
  have hle := hsum.le_tsum 0 (fun j _ => srwHeat_nonneg j (0 : Site d))
  have h0 : srwHeat d 0 (0 : Site d) = 1 := by simp
  calc (1 : ℝ) = srwHeat d 0 (0 : Site d) := h0.symm
    _ ≤ ∑' j : ℕ, srwHeat d j (0 : Site d) := hle

/-- The limiting variance is positive. -/
private theorem covN_self_pos (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (y : Site d) :
    0 < covN d ε y y := by
  by_cases hd2 : d = 2
  · simp only [covN, if_pos hd2]
    positivity
  · simp only [covN, if_neg hd2, sub_self, if_true]
    have hd3 : 3 ≤ d := by omega
    have := one_le_srwGreenInf_zero hd3
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have h2 : 0 < 2 * srwGreenInf d (0 : Site d) - 1 := by linarith
    exact mul_pos (by positivity) h2

/-- Quadratic forms of the limiting covariance are nonnegative. -/
private theorem covN_quad_nonneg (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {k : ℕ} (y : Fin k → Site d)
    (s : Fin k → ℝ) : 0 ≤ ∑ i, ∑ j, s i * s j * covN d ε (y i) (y j) := by
  by_cases hd2 : d = 2
  · have h1 : ∑ i, ∑ j, s i * s j * covN d ε (y i) (y j) =
        (∑ i, s i) * (∑ j, s j) * (16 * ε / Real.pi) := by
      simp only [covN, if_pos hd2]
      rw [Finset.sum_mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
    rw [h1]
    exact mul_nonneg (mul_self_nonneg _) (by positivity)
  · have h3 : 3 ≤ d := by omega
    obtain ⟨_, htsum⟩ := gamma_tsum_high h3 y s
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have h1 : ∑ i, ∑ j, s i * s j * covN d ε (y i) (y j) =
        2 * d * ε *
          ∑' x, gammaBr (combo (latticeKernel d) y s) (combo (latticeKernel d) y s) x := by
      rw [htsum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [covN, if_neg hd2]
      ring
    rw [h1]
    exact mul_nonneg (by positivity) (tsum_nonneg fun x => gammaBr_self_nonneg (by omega) _ x)

/-- The limiting covariance matrix is positive semidefinite. -/
private theorem covN_posSemidef (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {k : ℕ} (y : Fin k → Site d) :
    (Matrix.of fun i j => covN d ε (y i) (y j)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, covN_comm ε (y i) (y j)]
  · have h := covN_quad_nonneg hd hε y x
    have h2 : dotProduct (star x) ((Matrix.of fun i j => covN d ε (y i) (y j)).mulVec x) =
        ∑ i, ∑ j, x i * x j * covN d ε (y i) (y j) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h2]
    exact h


/-! ### The limit theorems at fixed sites -/

/-- The local time at a fixed site is a measurable function of the sample point. -/
private theorem measurable_localTime {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → Site d}
    (hX : ∀ n, Measurable (X n)) (n : ℕ) (y : Site d) :
    Measurable fun ω => (localTime (fun j => X j ω) n y : ℝ) := by
  have h : (fun ω => (localTime (fun j => X j ω) n y : ℝ)) =
      fun ω => ∑ j ∈ Finset.range n, (if X j ω = y then (1 : ℝ) else 0) := by
    funext ω
    exact (sum_ite_eq_localTime (fun j => X j ω) n y).symm
  rw [h]
  exact Finset.measurable_sum _ fun j _ =>
    Measurable.ite (hX j (measurableSet_singleton y)) measurable_const measurable_const

/-- The deviation of the local time at `y` from the profile, plus the local martingale at `y`,
divided by `σ_n`, tends to zero almost surely. -/
private theorem ae_potential_term_tendsto (hfluct : fluctuation_rates.{u})
    (hcenter : fixed_site_centering.{u}) (hmom : moment_fluctuations.{u})
    (hCLT : MartingaleCLT.{u}) (hLIL : StoutLIL.{u}) (hd : 2 ≤ d) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1 / (d : ℝ)) {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) (y : Site d) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => ((localTime (fun j => X j ω) n y : ℝ) -
        2 * d * ε * (radius d ε n - euclidNorm y) +
        dynkin ε (fun z => latticeKernel d (z - y)) X n ω) / sigmaN d ε n) atTop (𝓝 0) := by
  obtain ⟨Ct, hCt⟩ := ae_potential_term_le hfluct hcenter hmom hCLT hLIL hd hε0 hε1 μ hX y
  filter_upwards [hCt] with ω hω
  have hlim := (errScale_div_sigmaN hd hε0).const_mul Ct
  rw [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hω, (sigmaN_tendsto hd hε0).eventually_gt_atTop 0] with n hn hσ
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hσ, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hn hσ.le


/-- **The central limit theorem for combinations of fixed sites** (Step 4 with Step 5): for
`t : Fin k → ℝ`, the combination `Σ_i t_i (ℓ_n(y_i) - 2dε(r_n - |y_i|)) / σ_n` converges in
distribution to a centered Gaussian whose variance is the quadratic form of the covariance. -/
private theorem clt_combo (hshape : limit_shape.{u}) (hfluct : fluctuation_rates.{u})
    (hcenter : fixed_site_centering.{u}) (hmom : moment_fluctuations.{u})
    (hCLT : MartingaleCLT.{u}) (hLIL : StoutLIL.{u}) (hd : 2 ≤ d) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1 / (d : ℝ)) {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) {k : ℕ}
    (y : Fin k → Site d) (t : Fin k → ℝ) :
    TendstoInDistribution (fun n ω => ∑ i, t i * (((localTime (fun j => X j ω) n (y i) : ℝ) -
        2 * d * ε * (radius d ε n - euclidNorm (y i))) / sigmaN d ε n)) atTop id (fun _ => μ)
      (gaussianReal 0 (∑ i, ∑ j, t i * covN d ε (y i) (y j) * t j).toNNReal) := by
  obtain ⟨h, hK⟩ := exists_kernelFacts_latticeKernel hd
  obtain ⟨Cg, hg⟩ := hK.gradBound
  obtain ⟨C, hC⟩ := combo_grad_bound hg (by omega) y (fun i => -t i)
  obtain ⟨hS, hL2, h0, hinc⟩ := dynkin_martingale_facts (by omega) hε0.le hε1 hX hC
  have hquad : 0 ≤ ∑ i, ∑ j, (-t i) * (-t j) * covN d ε (y i) (y j) :=
    covN_quad_nonneg hd hε0 y _
  have hvar : ∑ i, ∑ j, (-t i) * (-t j) * covN d ε (y i) (y j) =
      ∑ i, ∑ j, t i * covN d ε (y i) (y j) * t j :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hbr := ae_bracket_tendsto hshape hd hε0 hε1 μ hX y (fun i => -t i)
  have hclt := tendstoInDistribution_of_bracket hCLT μ (pathFiltration hX.measurable)
    (dynkin ε (combo (latticeKernel d) y (fun i => -t i)) X) hS hL2 h0 (2 * C) hinc
    (sigmaN d ε) (sigmaN_tendsto hd hε0)
    (∑ i, ∑ j, (-t i) * (-t j) * covN d ε (y i) (y j)).toNNReal
    (by filter_upwards [hbr] with ω hω; rwa [Real.coe_toNNReal _ hquad])
  rw [hvar] at hclt
  have hE : ∀ᵐ ω ∂μ, ∀ i, Tendsto (fun n => ((localTime (fun j => X j ω) n (y i) : ℝ) -
        2 * d * ε * (radius d ε n - euclidNorm (y i)) +
        dynkin ε (fun z => latticeKernel d (z - y i)) X n ω) / sigmaN d ε n) atTop (𝓝 0) :=
    ae_all_iff.mpr fun i => ae_potential_term_tendsto hfluct hcenter hmom hCLT hLIL hd hε0 hε1
      μ hX (y i)
  have hYm : ∀ n, Measurable fun ω => ∑ i, t i * (((localTime (fun j => X j ω) n (y i) : ℝ) -
      2 * d * ε * (radius d ε n - euclidNorm (y i))) / sigmaN d ε n) := fun n =>
    Finset.measurable_sum _ fun i _ =>
      (((measurable_localTime hX.measurable n (y i)).sub measurable_const).div_const _).const_mul _
  have hXm : ∀ n, Measurable fun ω =>
      dynkin ε (combo (latticeKernel d) y (fun i => -t i)) X n ω / sigmaN d ε n := fun n =>
    (((hS.1 n).mono ((pathFiltration hX.measurable).le n)).measurable).div_const _
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hclt ?_ fun n => (hYm n).aemeasurable
  refine tendstoInMeasure_of_tendsto_ae (fun n => ((hYm n).sub (hXm n)).aestronglyMeasurable) ?_
  filter_upwards [hE] with ω hω
  have hsub : ∀ n, (∑ i, t i * (((localTime (fun j => X j ω) n (y i) : ℝ) -
        2 * d * ε * (radius d ε n - euclidNorm (y i))) / sigmaN d ε n)) -
        dynkin ε (combo (latticeKernel d) y (fun i => -t i)) X n ω / sigmaN d ε n =
      ∑ i, t i * (((localTime (fun j => X j ω) n (y i) : ℝ) -
        2 * d * ε * (radius d ε n - euclidNorm (y i)) +
        dynkin ε (fun z => latticeKernel d (z - y i)) X n ω) / sigmaN d ε n) := by
    intro n
    rw [dynkin_combo, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsum : Tendsto (fun n => ∑ i, t i * (((localTime (fun j => X j ω) n (y i) : ℝ) -
        2 * d * ε * (radius d ε n - euclidNorm (y i)) +
        dynkin ε (fun z => latticeKernel d (z - y i)) X n ω) / sigmaN d ε n)) atTop
      (𝓝 (∑ i : Fin k, t i * 0)) :=
    tendsto_finsetSum _ fun i _ => (hω i).const_mul (t i)
  simp only [mul_zero, Finset.sum_const_zero] at hsum
  refine hsum.congr fun n => ?_
  exact (hsub n).symm


/-- **The law of the iterated logarithm at a fixed site** (Step 4 with Step 5), for one sign. -/
private theorem lil_site (hshape : limit_shape.{u}) (hfluct : fluctuation_rates.{u})
    (hcenter : fixed_site_centering.{u}) (hmom : moment_fluctuations.{u})
    (hCLT : MartingaleCLT.{u}) (hLIL : StoutLIL.{u}) (hd : 2 ≤ d) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1 / (d : ℝ)) {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) (y : Site d) (sg : ℝ)
    (hsg : sg = 1 ∨ sg = -1) :
    ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ →
      (∀ᶠ n : ℕ in atTop, sg * ((localTime (fun j => X j ω) n y : ℝ) -
        2 * d * ε * (radius d ε n - euclidNorm y)) ≤
          (Real.sqrt (covN d ε y y) + δ) * lilN d ε n) ∧
      (∃ᶠ n : ℕ in atTop, (Real.sqrt (covN d ε y y) - δ) * lilN d ε n ≤
        sg * ((localTime (fun j => X j ω) n y : ℝ) -
          2 * d * ε * (radius d ε n - euclidNorm y))) := by
  obtain ⟨h, hK⟩ := exists_kernelFacts_latticeKernel hd
  obtain ⟨Cg, hg⟩ := hK.gradBound
  obtain ⟨C, hC⟩ := combo_grad_bound hg (by omega) (fun _ : Fin 1 => y) (fun _ => -sg)
  obtain ⟨hS, hL2, h0, hinc⟩ := dynkin_martingale_facts (by omega) hε0.le hε1 hX hC
  have hsq : sg * sg = 1 := by rcases hsg with rfl | rfl <;> norm_num
  have hbr := ae_bracket_tendsto hshape hd hε0 hε1 μ hX (fun _ : Fin 1 => y) (fun _ => -sg)
  have hbr' : ∀ᵐ ω ∂μ, Tendsto (fun n => predBracket μ (pathFiltration hX.measurable)
      (dynkin ε (combo (latticeKernel d) (fun _ : Fin 1 => y) (fun _ => -sg)) X)
      (dynkin ε (combo (latticeKernel d) (fun _ : Fin 1 => y) (fun _ => -sg)) X) n ω /
        sigmaN d ε n ^ 2) atTop (𝓝 (covN d ε y y)) := by
    filter_upwards [hbr] with ω hω
    have : ∑ i : Fin 1, ∑ j : Fin 1, (-sg) * (-sg) * covN d ε y y = covN d ε y y := by
      simp [hsq]
    rwa [this] at hω
  have hlil := lil_of_bracket hLIL μ (pathFiltration hX.measurable)
    (dynkin ε (combo (latticeKernel d) (fun _ : Fin 1 => y) (fun _ => -sg)) X) hS hL2 h0 (2 * C)
    hinc (sigmaN d ε) (lilN d ε) (sigmaN_tendsto hd hε0) (lilN_eq hd hε0) (loglog_sigmaN hd hε0)
    (covN d ε y y) (covN_self_pos hd hε0 y) hbr'
  have hE := ae_potential_term_tendsto hfluct hcenter hmom hCLT hLIL hd hε0 hε1 μ hX y
  filter_upwards [hlil, hE] with ω hlω hEω δ hδ
  have hσ := (sigmaN_tendsto hd hε0).eventually_gt_atTop 0
  have hLL : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (Real.log (n : ℝ)) :=
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop)).eventually_ge_atTop 1
  have hsmall : ∀ᶠ n : ℕ in atTop, |((localTime (fun j => X j ω) n y : ℝ) -
        2 * d * ε * (radius d ε n - euclidNorm y) +
        dynkin ε (fun z => latticeKernel d (z - y)) X n ω)| ≤ δ / 2 * lilN d ε n := by
    filter_upwards [(hEω.eventually (Metric.ball_mem_nhds 0 (by linarith : 0 < δ / 2))), hσ,
      lilN_eq hd hε0, hLL] with n hn hσn hl hLLn
    rw [dist_zero_right, Real.norm_eq_abs, abs_div, abs_of_pos hσn, div_lt_iff₀ hσn] at hn
    have hlge : sigmaN d ε n ≤ lilN d ε n := by
      rw [hl]
      calc sigmaN d ε n = Real.sqrt (sigmaN d ε n ^ 2) := (Real.sqrt_sq hσn.le).symm
        _ ≤ Real.sqrt (2 * sigmaN d ε n ^ 2 * Real.log (Real.log n)) := by
            apply Real.sqrt_le_sqrt
            nlinarith [sq_nonneg (sigmaN d ε n)]
    calc _ ≤ δ / 2 * sigmaN d ε n := hn.le
      _ ≤ δ / 2 * lilN d ε n := mul_le_mul_of_nonneg_left hlge (by linarith)
  have hrel : ∀ n : ℕ, dynkin ε (combo (latticeKernel d) (fun _ : Fin 1 => y) (fun _ => -sg))
      X n ω + sg * ((localTime (fun j => X j ω) n y : ℝ) -
        2 * d * ε * (radius d ε n - euclidNorm y) +
        dynkin ε (fun z => latticeKernel d (z - y)) X n ω) =
      sg * ((localTime (fun j => X j ω) n y : ℝ) - 2 * d * ε * (radius d ε n - euclidNorm y)) := by
    intro n
    rw [dynkin_combo]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    ring
  obtain ⟨hup, hlow⟩ := hlω (δ / 2) (by linarith)
  have habs : ∀ n : ℕ, |sg| = 1 := fun n => by rcases hsg with rfl | rfl <;> norm_num
  constructor
  · filter_upwards [hup, hsmall] with n hn1 hn2
    rw [← hrel n]
    have h3 : sg * (((localTime (fun j => X j ω) n y : ℝ) -
        2 * d * ε * (radius d ε n - euclidNorm y) +
        dynkin ε (fun z => latticeKernel d (z - y)) X n ω)) ≤ δ / 2 * lilN d ε n := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul, habs n, one_mul]
      exact hn2
    linarith
  · refine (hlow.and_eventually hsmall).mono fun n hn => ?_
    obtain ⟨hn1, hn2⟩ := hn
    rw [← hrel n]
    have h3 : -(δ / 2 * lilN d ε n) ≤ sg * (((localTime (fun j => X j ω) n y : ℝ) -
        2 * d * ε * (radius d ε n - euclidNorm y) +
        dynkin ε (fun z => latticeKernel d (z - y)) X n ω)) := by
      have := (abs_le.mp (by
        rw [abs_mul, habs n, one_mul]
        exact hn2 : |sg * (((localTime (fun j => X j ω) n y : ℝ) -
          2 * d * ε * (radius d ε n - euclidNorm y) +
          dynkin ε (fun z => latticeKernel d (z - y)) X n ω))| ≤ δ / 2 * lilN d ε n)).1
      exact this
    linarith


/-- **The central limit theorem at a fixed site**, in the notation of the proof. -/
private theorem clt_site (hshape : limit_shape.{u}) (hfluct : fluctuation_rates.{u})
    (hcenter : fixed_site_centering.{u}) (hmom : moment_fluctuations.{u})
    (hCLT : MartingaleCLT.{u}) (hLIL : StoutLIL.{u}) (hd : 2 ≤ d) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1 / (d : ℝ)) {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) (y : Site d) :
    TendstoInDistribution (fun n ω => ((localTime (fun j => X j ω) n y : ℝ) -
        2 * d * ε * (radius d ε n - euclidNorm y)) / sigmaN d ε n) atTop id (fun _ => μ)
      (gaussianReal 0 (covN d ε y y).toNNReal) := by
  have h := clt_combo hshape hfluct hcenter hmom hCLT hLIL hd hε0 hε1 μ hX (fun _ : Fin 1 => y)
    (fun _ => 1)
  simpa using h

end Helpers

/-- **Theorem 8.3** (`thm:site-fluctuations`): the central limit theorem, the law of the iterated
logarithm and the joint limits for the local times at fixed sites. -/
theorem site_fluctuations_of (hshape : limit_shape.{u})
    (hfluct : fluctuation_rates.{u}) (hcenter : fixed_site_centering.{u})
    (hmom : moment_fluctuations.{u}) : site_fluctuations.{u} := by
  intro d hd hCLT hLIL ωd ε hε0 hε1 r G σ lil v cov Ω _ μ _ X hX dev
  refine ⟨fun y => ?_, fun y => ?_, fun k y => ?_⟩
  · have hv : v = covN d ε y y := by
      simp only [v, covN, G, sub_self, if_true]
    have h := clt_site hshape hfluct hcenter hmom hCLT hLIL hd hε0 hε1 μ hX y
    convert h using 3
    all_goals first | exact hv | rfl
  · have hv : v = covN d ε y y := by
      simp only [v, covN, G, sub_self, if_true]
    rw [hv]
    filter_upwards [lil_site hshape hfluct hcenter hmom hCLT hLIL hd hε0 hε1 μ hX y 1 (Or.inl rfl),
      lil_site hshape hfluct hcenter hmom hCLT hLIL hd hε0 hε1 μ hX y (-1) (Or.inr rfl)]
      with ω h1 h2 δ hδ s hs
    rcases hs with rfl | rfl
    · exact h1 δ hδ
    · exact h2 δ hδ
  · have hV : ∀ n, AEMeasurable (fun ω => (WithLp.toLp 2 (fun i => dev (y i) n ω / σ n) :
        EuclideanSpace ℝ (Fin k))) μ := fun n =>
      ((MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurable.comp (measurable_pi_lambda _ fun i =>
        ((measurable_localTime hX.measurable n (y i)).sub
          measurable_const).div_const _)).aemeasurable
    refine tendstoInDistribution_vector μ _ hV (Matrix.of fun i j => covN d ε (y i) (y j))
      (covN_posSemidef hd hε0 y) fun t => ?_
    exact clt_combo hshape hfluct hcenter hmom hCLT hLIL hd hε0 hε1 μ hX y t

end CERW.Support.Limit
