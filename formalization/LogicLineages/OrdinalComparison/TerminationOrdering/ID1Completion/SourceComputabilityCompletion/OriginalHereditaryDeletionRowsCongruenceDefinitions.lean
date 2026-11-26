module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCongruence
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalClosedPrograms
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryDeletionRows
/-- An actual internally universally quantified cell law. The bound and both
input/parameter pairs are free arithmetic terms, not standard naturals. -/
def cellFields (Q : Program 2) {alpha : Type} (count input parameter other otherParameter index a b : OTerm alpha) : Formula alpha :=
 OriginalContextInsertion.Below index count ⊓
 (graph3 (observation Q) a index input parameter ⊓ graph3 (observation Q) b index other otherParameter)
def cellBody (Q : Program 2) {alpha : Type} (count input parameter other otherParameter : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
 (cellFields Q (count.relabel Sum.inl) (input.relabel Sum.inl) (parameter.relabel Sum.inl)
   (other.relabel Sum.inl) (otherParameter.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))).imp
   (equal (.var (.inr 1)) (.var (.inr 2)))
def CellAgreement (Q : Program 2) {alpha : Type} (count input parameter other otherParameter : OTerm alpha) : Formula alpha :=
 allBlock (cellBody Q count input parameter other otherParameter)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCongruence
