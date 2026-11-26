module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsBoundTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionParameterTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open OriginalContextInsertion (lengthGraph Below)
open OriginalClassContextAllPositionObserver (erasedPacked erasedParameter)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Off-diagonal deletion-row transport, with literal omitted-position reindex.
The two rows are NOT asserted equal. Intermediate context lengths are derived,
not hypotheses. No source, native calibration or covariance is supplied. This
does not discharge the additional zero cell introduced under lambda. -/
def ActualIndexedRowSquare : Prop := ∀ (Q : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (gamma count i j c parameter input upper upperParameter lower lowerParameter
  upperRow lowerRow upperValue lowerValue : OTerm alpha),
 Nonempty (Derivation body Delta
  ((lengthGraph (suc count) gamma ⊓
    (Below i (suc j) ⊓ (Below (suc j) (suc count) ⊓
     (graph2 InternalPairing.pairing parameter c gamma ⊓
      (graph3 erasedPacked upper (suc j) input parameter ⊓
       (graph3 erasedParameter upperParameter (suc j) input parameter ⊓
        (graph3 erasedPacked lower i input parameter ⊓
         (graph3 erasedParameter lowerParameter i input parameter ⊓
          (graph2 (OriginalHereditaryDeletionRows.rows Q) upperRow upper upperParameter ⊓
           (graph2 (OriginalHereditaryDeletionRows.rows Q) lowerRow lower lowerParameter ⊓
            (graph2 InternalRawListRecursion.lookup upperValue i upperRow ⊓
             graph2 InternalRawListRecursion.lookup lowerValue j lowerRow))))))))))).imp
    (equal upperValue lowerValue ⊓ (lengthGraph count upperRow ⊓ lengthGraph count lowerRow))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareTargets
