import CERW.Generic.Martingale.LilLower.Padding
import CERW.Generic.Martingale.LilLower.PaddedBracket
import CERW.Model.Bracket

/-!
# The predictable bracket of the padded process

The predictable bracket of a process is the sum of the conditional expectations of the squared
increments. For the padded process on the product it is, almost surely, the padded bracket of the
conditional variances of the original martingale, a function of the first coordinate only. While
the gate is open the padded bracket is the predictable bracket of the original martingale.
-/

namespace CERW.Generic.Martingale.LilLower

open MeasureTheory

variable {Ω : Type*} {Ξ : Type*} {m0 : MeasurableSpace Ω} {mΞ : MeasurableSpace Ξ}

/-- The predictable bracket is the sum of the conditional second moments of the increments. -/
theorem predBracket_eq_sum_condExp_sq (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S : ℕ → Ω → ℝ)
    (n : ℕ) :
    CERW.predBracket μ ℱ S S n =
      ∑ j ∈ Finset.range n, μ[fun ω => (S (j + 1) ω - S j ω) ^ 2 | ℱ j] := by
  unfold CERW.predBracket
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : (fun ω => (S (j + 1) ω - S j ω) * (S (j + 1) ω - S j ω)) =
      fun ω => (S (j + 1) ω - S j ω) ^ 2 := by
    funext ω
    ring
  rw [h]

/-- While the gate has been open at every time before `n`, the padded bracket built from the
conditional variances of `S` is the predictable bracket of `S`. -/
theorem paddedBracket_eq_predBracket_of_gate (μ : Measure Ω) (ℱ : Filtration ℕ m0)
    (S : ℕ → Ω → ℝ) {G : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω} (h : ∀ j < n, G j ω = 1) :
    paddedBracket (fun j ω => μ[fun ω => (S (j + 1) ω - S j ω) ^ 2 | ℱ j] ω) G n ω =
      CERW.predBracket μ ℱ S S n ω := by
  rw [paddedBracket_eq_of_gate h, predBracket_eq_sum_condExp_sq, Finset.sum_apply]

/-- The predictable bracket of the padded process is, almost surely, the padded bracket of the
conditional variances of the original martingale, evaluated at the first coordinate. -/
theorem predBracket_padded_ae_eq (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ)
    [IsProbabilityMeasure ν] (ℱ : Filtration ℕ m0) {𝒦 : ℕ → MeasurableSpace Ξ}
    {ε : ℕ → Ξ → ℝ} (hε : SignSequence ν 𝒦 ε) {S : ℕ → Ω → ℝ}
    (hL2 : ∀ n, MemLp (S n) 2 μ) {G : ℕ → Ω → ℝ}
    (hGm : ∀ j, StronglyMeasurable[ℱ j] (G j)) (hG01 : ∀ j ω, G j ω = 0 ∨ G j ω = 1) (n : ℕ) :
    CERW.predBracket (μ.prod ν) (liftFiltration ℱ 𝒦 hε.mono hε.le) (padded S G ε)
        (padded S G ε) n =ᵐ[μ.prod ν]
      fun z => paddedBracket (fun j ω => μ[fun ω => (S (j + 1) ω - S j ω) ^ 2 | ℱ j] ω) G n
        z.1 := by
  rw [predBracket_eq_sum_condExp_sq]
  have h : ∀ᵐ z ∂(μ.prod ν), ∀ j ∈ Finset.range n,
      (μ.prod ν)[fun z => (padded S G ε (j + 1) z - padded S G ε j z) ^ 2 |
        liftFiltration ℱ 𝒦 hε.mono hε.le j] z =
      G j z.1 * (μ[fun ω => (S (j + 1) ω - S j ω) ^ 2 | ℱ j]) z.1 + (1 - G j z.1) :=
    (Filter.eventually_all_finset _).2 fun j _ =>
      condExp_sq_increment_padded μ ν ℱ hε hL2 hGm hG01 j
  filter_upwards [h] with z hz
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl hz

end CERW.Generic.Martingale.LilLower
