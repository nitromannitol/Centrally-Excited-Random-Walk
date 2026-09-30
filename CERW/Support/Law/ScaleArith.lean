import CERW.Model.Kernel
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log

/-!
# Scale arithmetic for the probability bounds

Small bounds shared by the probability arguments: `1 ≤ log(n + 2)` for `n ≥ 2`; `1 ≤ C n^{-p}`
below a threshold `n₀` once `C ≥ n₀^p`; a union bound with a null set; the nonnegativity of a
gradient constant; the subadditivity of the square root; and the count of dyadic levels
`⌈log₂ max(Cg² n, 1)⌉ + 1 ≤ (Cg² + 3)(n + 1)`.
-/

namespace CERW.Support.Law

open MeasureTheory LatticeProb CERW

variable {d : ℕ}

/-- For `n ≥ 2` the logarithm `log (n + 2)` is at least `1`. -/
theorem one_le_log_add_two {n : ℕ} (hn : 2 ≤ n) : 1 ≤ Real.log ((n : ℝ) + 2) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_three
  linarith

/-- The bound `1 ≤ C n^{-p}` for `n ≤ n₀` once `C ≥ n₀^p`. -/
theorem one_le_mul_rpow_neg {C p : ℝ} {n n₀ : ℕ} (hp : 0 < p) (hn : 0 < n)
    (hnn : n ≤ n₀) (hC : (n₀ : ℝ) ^ p ≤ C) : 1 ≤ C * (n : ℝ) ^ (-p) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (n : ℝ) ^ p ≤ (n₀ : ℝ) ^ p :=
    Real.rpow_le_rpow hn'.le (Nat.cast_le.mpr hnn) hp.le
  have h2 : 0 < (n : ℝ) ^ p := Real.rpow_pos_of_pos hn' p
  rw [Real.rpow_neg hn'.le]
  calc (1 : ℝ) = (n : ℝ) ^ p * ((n : ℝ) ^ p)⁻¹ := (mul_inv_cancel₀ h2.ne').symm
    _ ≤ C * ((n : ℝ) ^ p)⁻¹ := mul_le_mul_of_nonneg_right (h1.trans hC) (inv_nonneg.mpr h2.le)

/-- A measure bound for a set covered by an event of small measure and a null event. -/
theorem measure_le_of_subset_union {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A N B : Set Ω} {a c : ENNReal} (hsub : B ⊆ A ∪ N) (hA : μ A ≤ a) (hN : μ N = 0)
    (hac : a ≤ c) : μ B ≤ c := by
  refine (measure_mono hsub).trans ((measure_union_le A N).trans ?_)
  rw [hN, add_zero]
  exact hA.trans hac

/-- The one-step bound forces `C_g ≥ 0`. -/
theorem cg_nonneg (hd : 1 ≤ d) {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ))) :
    0 ≤ Cg := by
  have h := hgrad 0 (unit ⟨0, by omega⟩) (mem_unitSteps.mpr ⟨⟨0, by omega⟩, Or.inl rfl⟩)
  have h' : |b (unit ⟨0, by omega⟩) - b 0| ≤ Cg := by simpa using h
  exact (abs_nonneg _).trans h'

/-- The square root of a sum is at most the sum of the square roots. -/
theorem sqrt_add_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- The base-two logarithm of `⌈W⌉₊`, plus one, is at most `(G + 3)(n + 1)` when
`W = max (G n) 1`, with `G = C²`. -/
theorem clog_ceil_add_one_le (Cg : ℝ) (n : ℕ) :
    ((Nat.clog 2 ⌈max (Cg ^ 2 * n) 1⌉₊ : ℕ) : ℝ) + 1 ≤ (Cg ^ 2 + 3) * ((n : ℝ) + 1) := by
  have hclog : Nat.clog 2 ⌈max (Cg ^ 2 * n) 1⌉₊ ≤ ⌈max (Cg ^ 2 * n) 1⌉₊ :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have h1 : ((Nat.clog 2 ⌈max (Cg ^ 2 * n) 1⌉₊ : ℕ) : ℝ) ≤ (⌈max (Cg ^ 2 * n) 1⌉₊ : ℝ) := by
    exact_mod_cast hclog
  have h2 := Nat.ceil_lt_add_one (zero_le_one.trans (le_max_right (Cg ^ 2 * (n : ℝ)) 1))
  have h3 : max (Cg ^ 2 * (n : ℝ)) 1 ≤ Cg ^ 2 * n + 1 := max_le (by linarith) (by
    have := mul_nonneg (sq_nonneg Cg) (Nat.cast_nonneg (α := ℝ) n)
    linarith)
  have h4 : (0 : ℝ) ≤ Cg ^ 2 := sq_nonneg _
  have h5 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

end CERW.Support.Law
