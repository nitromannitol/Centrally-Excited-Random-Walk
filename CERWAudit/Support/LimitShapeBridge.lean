import Mathlib
import CERW.Frozen.LimitShape
import CERWAudit.LimitShape.SolutionBasic

/-!
# Comparator bridge: `CERWAudit.LimitShape` vocabulary → repository

This file connects the statement-audit vocabulary of
`CERWAudit/LimitShape/Challenge.lean` (copied verbatim into
`CERWAudit/LimitShape/SolutionBasic.lean`, which imports only Mathlib) to the objects of the
repository `CERW`, so that `CERWAudit/LimitShape/Solution.lean` is literal gluing.

**It is imported by the `Solution` file only.**  The `Challenge` and `SolutionBasic` files
must stay Mathlib-only: a repository import inside the vocabulary changes instance
elaboration there and breaks the comparator's constant-by-constant closure check.

The audit vocabulary is already definitionally equal to the repository's — `Site` is
`Fin d → ℤ` on both sides, `euclidNorm`, `unit`, `stepProb`, `localTime`, `departureRange`
and `visitedRange` are token-for-token copies — so every bridge here is `rfl`; the sole
exception is the `Prop`-valued structure `IsCERW`, whose two copies are interderivable but
not the same inductive, so the bridge packs and unpacks it field by field.
-/

universe u

namespace CERWAudit
namespace Support
namespace LimitShapeBridge

open MeasureTheory

/-- The audit vocabulary agrees with the repository definitionally.  These `rfl` lemmas
record the identifications the solution relies on. -/
theorem euclidNorm_eq (d : ℕ) (x : CERW.StatementAudit.LimitShape.Site d) :
    CERW.StatementAudit.LimitShape.euclidNorm x = LatticeProb.euclidNorm x := rfl

theorem localTime_eq {d : ℕ} (X : ℕ → CERW.StatementAudit.LimitShape.Site d) (n : ℕ)
    (x : CERW.StatementAudit.LimitShape.Site d) :
    CERW.StatementAudit.LimitShape.localTime X n x = CERW.localTime X n x := rfl

theorem departureRange_eq {d : ℕ} (X : ℕ → CERW.StatementAudit.LimitShape.Site d) (n : ℕ) :
    CERW.StatementAudit.LimitShape.departureRange X n = CERW.departureRange X n := rfl

theorem visitedRange_eq {d : ℕ} (X : ℕ → CERW.StatementAudit.LimitShape.Site d) (n : ℕ) :
    CERW.StatementAudit.LimitShape.visitedRange X n = CERW.visitedRange X n := rfl

/-- The challenge's CERW law and the repository's are the same predicate.  The two
structures have the same fields, and the one-step kernel `stepProb` (and hence every field)
is definitionally equal, so the conversion only packs and unpacks the `Prop`-valued
structure. -/
theorem isCERW_iff {d : ℕ} {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {ε : ℝ}
    {X : ℕ → Ω → CERW.StatementAudit.LimitShape.Site d} :
    CERW.StatementAudit.LimitShape.IsCERW μ ε X ↔ CERW.IsCERW μ ε X := by
  constructor
  · rintro ⟨hm, hs, hst⟩
    exact ⟨hm, hs, hst⟩
  · rintro ⟨hm, hs, hst⟩
    exact ⟨hm, hs, hst⟩

end LimitShapeBridge
end Support
end CERWAudit
