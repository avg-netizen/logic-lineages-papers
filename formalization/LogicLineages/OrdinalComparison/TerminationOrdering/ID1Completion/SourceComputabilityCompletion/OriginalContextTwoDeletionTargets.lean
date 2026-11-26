module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open OriginalClassContextAllPositionObserver (deleteAt)
open OriginalContextInsertion (lengthGraph Below)
/-- Actual graph commutation and the two matching erased type lookups.
Both positions belong to the original encoded context, with i < suc j.
No decoded-list, insertion, source, or native equality premise is supplied.
The four deletion graphs are the literal pre-existing deleteAt Program. -/
def ActualContextSquare : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (gamma count i j a b upper lower left right : OTerm alpha),
  Nonempty (Derivation body Delta
    ((lengthGraph count gamma ⊓
      (Below i (suc j) ⊓ (Below (suc j) count ⊓
       (graph2 InternalRawListRecursion.lookup a i gamma ⊓
        (graph2 InternalRawListRecursion.lookup b (suc j) gamma ⊓
         (graph2 deleteAt upper (suc j) gamma ⊓
          (graph2 deleteAt left i upper ⊓
           (graph2 deleteAt lower i gamma ⊓ graph2 deleteAt right j lower)))))))).imp
      (equal left right ⊓
       (graph2 InternalRawListRecursion.lookup a i upper ⊓
        graph2 InternalRawListRecursion.lookup b j lower))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionTargets
