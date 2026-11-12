module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRow
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalClosedPrograms (allBlock)
open OriginalHereditaryInternalAgenda
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Internal bounded lookup assertion for an untagged encoded job row. -/
def jobsMatrix {alpha : Type} (H : Program 1) (M W : Program 2) (c B row : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
 (lookupFields (row.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))).imp
 (Job H M W (c.relabel Sum.inl) (B.relabel Sum.inl) (.var (.inr 2)))
def Jobs {alpha : Type} (H : Program 1) (M W : Program 2) (c B row : OTerm alpha) : Formula alpha :=
 allBlock (jobsMatrix H M W c B row)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRow
