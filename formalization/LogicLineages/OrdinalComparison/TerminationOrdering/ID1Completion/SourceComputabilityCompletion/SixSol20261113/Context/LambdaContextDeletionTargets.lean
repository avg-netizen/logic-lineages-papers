module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaContextProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphExtensionSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.LambdaContextDeletionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
/-- Pure original cons/list metadata. Count is symbolic and no source or E
relation is assumed. Instantiate count with suc n for context-length induction. -/
def ActualMetadata : Prop :=
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (gamma deleted childGamma childDeleted domain cutoff erasedType count : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode childGamma domain gamma)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode childDeleted domain deleted)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count gamma)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff count)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup erasedType cutoff gamma)) →
 Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff gamma)) →
 Nonempty (Derivation body Delta
   (OriginalContextInsertion.lengthGraph (suc count) childGamma ⊓
    (OriginalContextInsertion.Below (suc cutoff) (suc count) ⊓
     (graph2 InternalRawListRecursion.lookup erasedType (suc cutoff) childGamma ⊓
      graph2 OriginalClassContextAllPositionObserver.deleteAt childDeleted (suc cutoff) childGamma))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.LambdaContextDeletionTargets
