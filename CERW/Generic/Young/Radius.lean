import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Inverting the radius equation

The inradius is determined through `|1 - c (b/N)^{d+1}| ≤ C Q` (`eq:inradius`), where
`c a^{d+1} = 1`. Since `t^p - a^p = (t - a) Σ_{i<p} t^i a^{p-1-i}` and the sum is at least
`a^{p-1}` for `t ≥ 0`, the root is Lipschitz: `|t - a| ≤ a |1 - c t^p|`.
-/

namespace CERW.Generic.Young

/-- For `t ≥ 0`, `a > 0` and `p ≥ 1`,
`|t - a| ≤ |t^p - a^p| / a^{p-1}`. -/
theorem abs_sub_le_abs_pow_sub_div {t a : ℝ} (ht : 0 ≤ t) (ha : 0 < a) {p : ℕ} (hp : 1 ≤ p) :
    |t - a| ≤ |t ^ p - a ^ p| / a ^ (p - 1) := by
  have hterm : ∀ i ∈ Finset.range p, 0 ≤ t ^ i * a ^ (p - 1 - i) :=
    fun i _ => mul_nonneg (pow_nonneg ht i) (pow_nonneg ha.le (p - 1 - i))
  have hle : a ^ (p - 1) ≤ ∑ i ∈ Finset.range p, t ^ i * a ^ (p - 1 - i) := by
    have := Finset.single_le_sum (s := Finset.range p)
      (f := fun i => t ^ i * a ^ (p - 1 - i)) hterm (Finset.mem_range.mpr hp)
    simpa [pow_zero, one_mul, Nat.sub_zero] using this
  have hsum_nonneg : 0 ≤ ∑ i ∈ Finset.range p, t ^ i * a ^ (p - 1 - i) :=
    Finset.sum_nonneg hterm
  have hgeom : (∑ i ∈ Finset.range p, t ^ i * a ^ (p - 1 - i)) * (t - a) = t ^ p - a ^ p :=
    geom_sum₂_mul t a p
  have hpos : 0 < a ^ (p - 1) := pow_pos ha (p - 1)
  rw [le_div_iff₀' hpos]
  calc
    a ^ (p - 1) * |t - a| ≤ (∑ i ∈ Finset.range p, t ^ i * a ^ (p - 1 - i)) * |t - a| :=
      mul_le_mul_of_nonneg_right hle (abs_nonneg (t - a))
    _ = |(∑ i ∈ Finset.range p, t ^ i * a ^ (p - 1 - i)) * (t - a)| := by
      rw [abs_mul, abs_of_nonneg hsum_nonneg]
    _ = |t ^ p - a ^ p| := by rw [hgeom]

/-- If `c a^p = 1` with `a > 0`, `p ≥ 1` and `t ≥ 0`, then `|1 - c t^p| ≤ η` forces
`|t - a| ≤ a η`. -/
theorem abs_sub_le_of_abs_one_sub_mul_pow {c t a η : ℝ} (ht : 0 ≤ t) (ha : 0 < a) {p : ℕ}
    (hp : 1 ≤ p) (hca : c * a ^ p = 1) (h : |1 - c * t ^ p| ≤ η) : |t - a| ≤ a * η := by
  have hap : 0 < a ^ p := pow_pos ha p
  have hcinv : c⁻¹ = a ^ p := inv_eq_of_mul_eq_one_right hca
  have hc : 0 < c := by rw [← inv_pos, hcinv]; exact hap
  have hpos : 0 < a ^ (p - 1) := pow_pos ha (p - 1)
  have hsub : 1 - c * t ^ p = c * (a ^ p - t ^ p) := by rw [mul_sub, hca]
  have hcabs : c * |a ^ p - t ^ p| = |1 - c * t ^ p| := by
    rw [hsub, abs_mul, abs_of_pos hc]
  have hmul : c * |a ^ p - t ^ p| ≤ η := by rw [hcabs]; exact h
  have hle_div : |a ^ p - t ^ p| ≤ η / c := (le_div_iff₀ hc).mpr (by
    rw [mul_comm]; exact hmul)
  have hdiv_eq : η / c = a ^ p * η := by rw [div_eq_mul_inv, hcinv, mul_comm]
  have h1 : |a ^ p - t ^ p| ≤ a ^ p * η := by rw [hdiv_eq] at hle_div; exact hle_div
  have hpow : a ^ p = a ^ (p - 1) * a := by
    conv_lhs => rw [← Nat.sub_add_cancel hp]
    rw [pow_succ]
  have hbase : |t - a| ≤ |t ^ p - a ^ p| / a ^ (p - 1) :=
    abs_sub_le_abs_pow_sub_div ht ha hp
  have hdiv : |a ^ p - t ^ p| / a ^ (p - 1) ≤ a * η := by
    rw [div_le_iff₀ hpos]
    calc
      |a ^ p - t ^ p| ≤ a ^ p * η := h1
      _ = a * η * a ^ (p - 1) := by rw [hpow]; ring
  calc
    |t - a| ≤ |t ^ p - a ^ p| / a ^ (p - 1) := hbase
    _ = |a ^ p - t ^ p| / a ^ (p - 1) := by rw [abs_sub_comm]
    _ ≤ a * η := hdiv

end CERW.Generic.Young
