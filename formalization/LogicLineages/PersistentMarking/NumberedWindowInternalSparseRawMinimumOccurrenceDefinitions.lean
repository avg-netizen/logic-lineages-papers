module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawMinimumOccurrence
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (existsOne)
open NumberedWindowInternalSparseFieldParserTargets (parserGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc unary)
open NumberedWindowInternalSparseOrderedMinimum (orderedPoolMinimum scratchMinimum)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

/-- The exact unchanged executable on the original sparse raw input. -/
def rawMinimumGraph {α : Type} (raw selected : OTerm α) : Formula α :=
  unary orderedPoolMinimum (suc selected) raw

/-- One physical parser output supplies the same decoded scratch term
to the real minimum graph and the real occurrence checker. -/
def parsedOccurrenceRow {α : Type} (raw scratch selected : OTerm α) : Formula α :=
  parserGraph (suc scratch) raw ⊓
    (unary scratchMinimum (suc selected) scratch ⊓ memberGraph scratch selected)

def parsedOccurrence {α : Type} (raw selected : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  existsOne (parsedOccurrenceRow (raw.relabel j) (.var (.inr 0)) (selected.relabel j))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawMinimumOccurrence
