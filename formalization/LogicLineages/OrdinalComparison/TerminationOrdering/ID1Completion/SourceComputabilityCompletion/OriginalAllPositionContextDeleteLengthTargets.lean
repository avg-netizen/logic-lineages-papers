module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteLengthTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
/-- Literal in-range deletion removes exactly one numeric context entry. -/
def ActualLength : Prop :=
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
   (gamma count cutoff deleted : OTerm alpha),
 Nonempty (Derivation body Delta
  ((OriginalContextInsertion.lengthGraph (suc count) gamma ⊓
    (OriginalContextInsertion.Below cutoff (suc count) ⊓
     graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff gamma)).imp
   (OriginalContextInsertion.lengthGraph count deleted)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteLengthTargets
