module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineGuardLeafDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineNonBottom
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)

/-- The literal existing bottom-spine guard rejects every literal packed
bottom source. Its measure is flagged with depth zero, so its strict-decrease
branch cannot accept. No validity, endpoint typing, native reflection or
selected-program premise is added. This supplies the distinct non-bottom
factor of the original guarded positive checker, not an H+ certificate. -/
def SpineGuardRejectsBottom : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (source target certificate parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((OriginalSpineGuardLeaf.spineAccepted source target certificate parameter).imp
      ((BottomRepresentative.bottomGraph InternalOriginalStepGuard.one source).not)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineNonBottom
