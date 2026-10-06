/-
# The local radial-singularity estimate for the unrestricted Newton convolution: the tail half

`CERW.Support.Norm.integral_weight_inner_newtonField` (`ContactPotential.lean:2278`) proves the
radial
Newton convolution identity for a radial weight `χ` that carries a global bound `hM : ∀ s, χ s ≤ M`.
Dropping `hM` needs the integrability of `χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - d)`; that is what this module starts.

The estimate has two halves, and they have very different status:

* **Tail half (this module).**  On `{ζ | 1 ≤ ‖w - ζ‖}` the Newton kernel is bounded by `1`, so the
  weighted integrand is dominated by the integrable `χ ‖·‖` and the `IntegrableOn` follows from
  `hχi` alone — no bound on `χ` is needed.  The only side condition is the (Mathlib-dischargeable)
  measurability of the weighted integrand, taken here as an explicit hypothesis.
* **Local half (NOT proved, and NOT provable as stated).**  On `Metric.ball w 1` the kernel norm
  `‖w - ζ‖ ^ (1 - d)` is only marginally integrable at `ζ = w`, and a merely integrable radial weight
  can make the product non-integrable: the polar form centred at `w` makes the integral
  `∫_0^1 (∫_θ χ ‖w + ρ θ‖ dθ) dρ`, and a radial spike of height `h` and radial width `δ` at radius
  `‖w‖ + δ` contributes `≈ h δ log (1/δ)`, while `∫ χ` only sees `≈ h δ`.  Spikes with
  `δ_k = e^{-k}` and `h_k = e^{k} / k²` therefore keep `∫ χ < ∞` but make the local integral
  diverge (`Σ_k k / k² = ∞`).  So the local half needs an extra hypothesis — `χ` bounded near `‖w‖`
  (the library's `hM`), or `χ` nonincreasing in the radius near `‖w‖`.
-/
import Mathlib

open MeasureTheory

namespace CERW.Support.Norm

/-- **The Newton kernel is bounded by `1` off the unit ball.**  For `1 ≤ d` and `1 ≤ ‖w - ζ‖`,
`‖w - ζ‖ ^ (1 - d) ≤ 1`. -/
theorem rpow_norm_sub_le_one_of_one_le {d : ℕ} (hd : 1 ≤ d)
    {w ζ : EuclideanSpace ℝ (Fin d)} (h : 1 ≤ ‖w - ζ‖) :
    ‖w - ζ‖ ^ (1 - (d : ℝ)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos h (by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith)

/-- **Tail half of the local radial-singularity estimate.**  Off the unit ball around `w` the Newton
kernel has norm at most `1`, so `ζ ↦ χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - d)` is dominated by the integrable
`ζ ↦ χ ‖ζ‖`: no bound on `χ` is used. -/
theorem integrableOn_weight_mul_newtonKernel_tail {d : ℕ} (hd : 1 ≤ d) {χ : ℝ → ℝ}
    {w : EuclideanSpace ℝ (Fin d)} (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    (hmeas : AEStronglyMeasurable
      (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ)))
      (volume.restrict {ζ : EuclideanSpace ℝ (Fin d) | 1 ≤ ‖w - ζ‖})) :
    IntegrableOn (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ)))
      {ζ : EuclideanSpace ℝ (Fin d) | 1 ≤ ‖w - ζ‖} := by
  refine (hχi.integrableOn).mono' hmeas ?_
  filter_upwards [ae_restrict_mem (measurableSet_le measurable_const (by fun_prop))] with ζ hζ
  have hrpow : ‖w - ζ‖ ^ (1 - (d : ℝ)) ≤ 1 := rpow_norm_sub_le_one_of_one_le hd hζ
  have hnn : 0 ≤ χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ)) :=
    mul_nonneg (hχ0 _) (Real.rpow_nonneg (norm_nonneg _) _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ)) ≤ χ ‖ζ‖ * 1 :=
        mul_le_mul_of_nonneg_left hrpow (hχ0 _)
    _ = χ ‖ζ‖ := mul_one _

end CERW.Support.Norm
