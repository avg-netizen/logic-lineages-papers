module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawMinimumOccurrenceDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawMinimumOccurrenceTargets
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalSparseRawMinimumOccurrence

/-- Successful actual raw-pool minimum yields one genuine internal
scratch witness at the same raw code, not a semantic decode assumption. -/
def ExactOpenRawMinimumParsedOccurrence : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (raw selected : OTerm α),
    Nonempty (Derivation body Γ ((rawMinimumGraph raw selected).imp (parsedOccurrence raw selected)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawMinimumOccurrenceTargets
