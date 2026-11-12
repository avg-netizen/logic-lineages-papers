module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaGeometryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SourceComputabilityFormulaSupportProof (numeral)
/-- Supporting shifted-row implication only. Equal tails of child deletion rows
exclude their genuinely new zero cell. Full lambda/body-type/context graphs
are actual premises, not inferred from a constructor that discards child type.
No source-class coherence or unrestricted covariance is asserted. -/
def ShiftedLambdaRows : Prop := ∀ (Q : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input other domain codomain child otherChild parameter childParameter
  c gamma extended count childRow otherChildRow tail otherTail row otherRow : OTerm alpha),
 Nonempty (Derivation body Delta
  ((OriginalLambdaTraversalInternal.LambdaFields input domain codomain child parameter childParameter ⊓
    (OriginalLambdaTraversalInternal.LambdaFields other domain codomain otherChild parameter childParameter ⊓
     (graph3 OriginalLambdaConstructor.constructor input domain codomain child ⊓
      (graph3 OriginalLambdaConstructor.constructor other domain codomain otherChild ⊓
       (graph2 InternalPairing.pairing parameter c gamma ⊓
        (OriginalContextInsertion.lengthGraph count gamma ⊓
         (graph2 InternalListCodec.consCode extended domain gamma ⊓
          (graph2 InternalPairing.pairing childParameter c extended ⊓
           (graph2 (OriginalHereditaryDeletionRows.rows Q) childRow child childParameter ⊓
            (graph2 (OriginalHereditaryDeletionRows.rows Q) otherChildRow otherChild childParameter ⊓
             (graph2 InternalRawListRecursion.drop tail (numeral 1) childRow ⊓
              (graph2 InternalRawListRecursion.drop otherTail (numeral 1) otherChildRow ⊓
               (equal tail otherTail ⊓
                (graph2 (OriginalHereditaryDeletionRows.rows (OriginalRootObservation.rootObservation Q)) row input parameter ⊓
                 graph2 (OriginalHereditaryDeletionRows.rows (OriginalRootObservation.rootObservation Q)) otherRow other parameter)))))))))))))).imp
    (equal row otherRow)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaTargets
