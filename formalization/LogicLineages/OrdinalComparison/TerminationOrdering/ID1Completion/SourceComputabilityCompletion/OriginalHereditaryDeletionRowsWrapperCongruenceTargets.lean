module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCongruenceTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsWrapperCongruenceTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryDeletionRows OriginalHereditaryDeletionRowsCongruence
/-- Same actual context length, explicitly witnessed on both runtime parameters.
No claim that arbitrary context transformations preserve these premises. -/
def RowsCongruence : Prop := ∀ (Q : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (count input parameter gamma other otherParameter otherGamma row otherRow : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 InternalUnpair.right gamma parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count gamma)) →
 Nonempty (Derivation body Delta (graph1 InternalUnpair.right otherGamma otherParameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count otherGamma)) →
 Nonempty (Derivation body Delta (CellAgreement Q count input parameter other otherParameter)) →
 Nonempty (Derivation body Delta (graph2 (rows Q) row input parameter)) →
 Nonempty (Derivation body Delta (graph2 (rows Q) otherRow other otherParameter)) →
 Nonempty (Derivation body Delta (equal row otherRow))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsWrapperCongruenceTargets
