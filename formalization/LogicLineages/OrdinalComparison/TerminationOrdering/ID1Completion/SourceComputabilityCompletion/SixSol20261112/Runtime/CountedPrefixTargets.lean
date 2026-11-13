module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalAdditionLawsProof (add)
/-- Actual take/drop computations at a genuinely available symbolic count
reassemble the SAME original row and have the exact two lengths. No append,
prefix/suffix lengths, partition law or native decoding is supplied. This
recovers the return-stack partition from total completed-result length. -/
def ActualCountedSplit : Prop :=
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (count remaining row front suffix : OTerm alpha),
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (add count remaining) row)) →
 Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.front front count row)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.drop suffix count row)) →
 Nonempty (Derivation body Delta
   (OriginalContextInsertion.lengthGraph count front ⊓
    (OriginalContextInsertion.lengthGraph remaining suffix ⊓
     graph2 InternalApplicationValidityStackAppend.append row front suffix)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixTargets
