module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.SuffixLookupTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalAdditionLawsProof (add)
/-- The literal suffix of the original total lookup at its actual append offset.
All cutoffs, including those beyond the suffix length, retain their original
default-value behavior. No index correspondence, range or semantic premise. -/
def ActualUnboundedSuffixLookup : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (frontLength front suffix joined cutoff value : OTerm alpha),
  Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph frontLength front)) →
  Nonempty (Derivation body Delta
    (graph2 InternalApplicationValidityStackAppend.append joined front suffix)) →
  Nonempty (Derivation body Delta
    ((graph2 InternalRawListRecursion.lookup value (add frontLength cutoff) joined).iff
      (graph2 InternalRawListRecursion.lookup value cutoff suffix)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.SuffixLookupTargets
