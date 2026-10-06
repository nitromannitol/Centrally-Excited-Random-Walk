import CERW.Frozen.ExpDeviation
import CERW.Support.Lower.ExpDeviationStatement
import CERW.Support.Lower.SharpWidth
import CERW.Support.Lower.SharpRadii
import CERW.Support.Lower.SharpBulk
import CERW.Support.Main.LimitShape

/-!
# Consumers of the exponential deviation lemma

The lower bounds of `thm:sharp` take the exponential deviation lemma as the hypothesis
`CERW.Support.Statements.exp_deviation_upTo`, the statement of `CERW.Frozen.exp_deviation`. Each consumer
applies it to its own martingale: the polynomial lower bound of the width to the first coordinate of the
compensated position, the lower bounds of the radii to the truncated quadratic martingale, and the lower bound
of the local times near the origin to the family of the normalized Dynkin martingales, with their adaptation,
integrability, conditional means, almost sure increments and brackets read from those martingales. Here the
hypothesis is supplied by the frozen export itself.
-/

universe u

namespace CERW.Support.Guards

open CERW.Support.Statements

/-- The frozen export is the hypothesis of the consumers. -/
theorem exp_deviation_upTo_of_frozen : exp_deviation_upTo.{u} := @CERW.Frozen.exp_deviation.{u}

/-- Part (iv) of `thm:sharp` for the radii in the plane: the lower bound of the limsup and the polynomial
lower bound, from the frozen exponential deviation lemma. -/
theorem sharp_width_of_frozen : sharp_width.{u} :=
  CERW.Support.Lower.sharp_width_of (@CERW.Support.Main.limit_shape.{u}) exp_deviation_upTo_of_frozen.{u}

/-- Part (i) of `thm:sharp`: the polynomial lower bounds for the radii in the plane, from the frozen
exponential deviation lemma. -/
theorem sharp_radii_of_frozen (hfluct : fluctuation_rates.{u}) : sharp_radii.{u} :=
  CERW.Support.Lower.sharp_radii_of hfluct exp_deviation_upTo_of_frozen.{u}

/-- Part (iii) of `thm:sharp`: the lower bound of the local times near the origin, from the frozen
exponential deviation lemma. -/
theorem sharp_bulk_of_frozen (hsep : separated_brackets.{u}) (hfluct : fluctuation_rates.{u}) :
    sharp_bulk.{u} :=
  CERW.Support.Lower.sharp_bulk_of hsep exp_deviation_upTo_of_frozen.{u} hfluct

end CERW.Support.Guards
