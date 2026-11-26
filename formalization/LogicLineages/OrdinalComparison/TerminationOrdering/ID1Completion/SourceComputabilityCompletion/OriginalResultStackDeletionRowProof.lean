module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackDeletionRowTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackSlotsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackDeletionRowProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof (projectionValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
theorem actualRestoration : OriginalResultStackDeletionRowTargets.ActualRestoration := by
 intro body alpha Delta children count row reversed suffix stack hl hr ha
 obtain ⟨laws⟩ := OriginalReverseLengthInvolutionProof.actualLaws body alpha Delta row count reversed hl hr
 have hlen : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count reversed)) :=
   ⟨Derivation.conjunctionLeft laws⟩
 have hback : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse row reversed)) :=
   ⟨Derivation.conjunctionRight laws⟩
 obtain ⟨part⟩ := OriginalResultStackPartitionProof.actualPartition body alpha Delta count reversed suffix stack hlen ha
 let xs : Fin 3 → OTerm alpha := ![children,count,stack]
 have hf : Nonempty (Derivation body Delta
   (graph3 OriginalHereditaryResultStackProgram.deletionFront reversed children count stack)) :=
   binaryValue OriginalClassContextAllPositionObserver.front (.projection 1) (.projection 2)
     reversed count stack xs ⟨Derivation.conjunctionLeft part⟩ (projectionValue 1 xs) (projectionValue 2 xs)
 exact unaryValue OriginalTypedArgumentObservations.reverse OriginalHereditaryResultStackProgram.deletionFront
   row reversed xs hback hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackDeletionRowProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackDeletionRowProof
