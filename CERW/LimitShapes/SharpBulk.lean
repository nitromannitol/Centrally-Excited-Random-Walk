module

public import CERW.LimitShapes.Frozen.EuclideanSeparatedBrackets
public import CERW.LimitShapes.Frozen.ExpDeviation
public import CERW.LimitShapes.BulkPotential
public import CERW.Support.Lower.SharpBulk

@[expose] public section

/-!
# Sharp bulk deviations from the excess potential

The closed source result for Theorem `thm:sharp` (iii) combines common-event separated
brackets, Lemma `lem:exp-deviation`, and the actual excess-set bulk potential estimate
`eq:bulk-potential-only`. The pointwise Dynkin argument then gives a large local-time
deviation near the origin with polynomially small failure probability.
-/

universe u

open MeasureTheory

namespace CERW.LimitShapes.SharpBulk

/-- The common-event bracket bounds imply the older probability interface, by containing
bracket failure in the event complement almost everywhere. Constants precede the law. -/
theorem separated_brackets_from_common_event : CERW.Support.Statements.separated_brackets.{u} := by
  intro d hd ωd ε hε0 hε1 r e₁ g σ k m y f
  obtain ⟨K, _, _, _, _, _, _, _, c₀, C₀, C, hc₀, hC₀, hC, n₀, _, hbounds⟩ :=
    CERW.LimitShapes.separated_brackets_on_euclidean_event.{u} hd ε hε0 hε1
  refine ⟨c₀, C₀, C, hc₀, hC₀, hC, n₀, ?_⟩
  intro Ω _ μ _ X hX n hn
  obtain ⟨hprob, hae⟩ := hbounds μ X hX n hn
  refine (measure_mono_ae ?_).trans hprob
  filter_upwards [hae] with ω hω
  intro hfail hgood
  exact hfail (hω hgood)

end CERW.LimitShapes.SharpBulk

/-- Theorem `thm:sharp` (iii), from the common-event bracket bounds, exponential martingale
deviation, and the excess-set estimate `eq:bulk-potential-only`. -/
theorem CERW.LimitShapes.sharp_bulk_from_common_event :
    CERW.Support.Statements.sharp_bulk.{u} := by
  exact CERW.Support.Lower.sharp_bulk_of_potential
    CERW.LimitShapes.SharpBulk.separated_brackets_from_common_event
    CERW.LimitShapes.exp_deviation
    CERW.LimitShapes.bulk_potential_only_from_excess
