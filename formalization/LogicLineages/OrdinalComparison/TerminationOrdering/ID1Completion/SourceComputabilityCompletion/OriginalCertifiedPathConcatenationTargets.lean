module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual certified path composition for any literal edge checker, using
original numeric append. No semantic edge law or native premise. -/
def ActualConcatenation : Prop := ∀ (edge : Program 3) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha)) (left source middle target right combined : OTerm alpha),
 Nonempty (Derivation body Delta (InternalPathChecker.pathGraph edge source middle left)) →
 Nonempty (Derivation body Delta (InternalPathChecker.pathGraph edge middle target right)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append combined left right)) →
 Nonempty (Derivation body Delta (InternalPathChecker.pathGraph edge source target combined))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationTargets
