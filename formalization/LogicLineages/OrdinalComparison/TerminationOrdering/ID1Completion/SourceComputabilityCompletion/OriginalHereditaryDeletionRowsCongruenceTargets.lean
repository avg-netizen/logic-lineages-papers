module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCongruenceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCongruenceTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryDeletionRows OriginalHereditaryDeletionRowsCongruence
/-- Generic internal supplier only. No source covariance or final hereditary
preservation is asserted; the quantified in-range cell law remains explicit. -/
def ScanCongruence : Prop := ∀ (Q : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (count input parameter other otherParameter row otherRow : OTerm alpha),
 Nonempty (Derivation body Delta
   ((CellAgreement Q count input parameter other otherParameter ⊓
     (graph3 (scan Q) row count input parameter ⊓ graph3 (scan Q) otherRow count other otherParameter)).imp
     (equal row otherRow)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCongruenceTargets
