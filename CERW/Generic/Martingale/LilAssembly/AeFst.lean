import CERW.Generic.Martingale.LilAssembly.Statements

/-!
# Almost everywhere along the first coordinate

A property of the first coordinate that holds almost everywhere on `μ.prod ν`, with `ν` a
probability measure, holds `μ`-almost everywhere.
-/

universe u v

namespace CERW.Generic.Martingale.LilAssembly

open MeasureTheory ProbabilityTheory Filter Topology

/-- From almost everywhere on a product to almost everywhere on the first factor. -/
theorem ae_fst_of_ae_prod : AeFstOfAeProd.{u, v} := by
  intro Ω Ξ _ _ μ ν _ _ p h
  rw [ae_iff] at h ⊢
  have h1 : {z : Ω × Ξ | ¬ p z.1} = {ω | ¬ p ω} ×ˢ (Set.univ : Set Ξ) := by
    ext z
    simp
  rw [h1, Measure.prod_prod, measure_univ, mul_one] at h
  exact h

end CERW.Generic.Martingale.LilAssembly
