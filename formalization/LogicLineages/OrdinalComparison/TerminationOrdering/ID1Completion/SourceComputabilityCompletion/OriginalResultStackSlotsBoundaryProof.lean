module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackSlotsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackSlotsBoundaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem boundary : OriginalResultStackSlotsTargets.Boundary := by
 intro body alpha Delta count initialList suffix joined value hl ha hh
 have hp := OriginalResultStackPartitionProof.actualPartition body alpha Delta count initialList suffix joined hl ha
 exact InternalRawListRecursionSupportProof.lookupValue value count joined suffix
   (InternalApplicationStepPeelSupportProof.andRight hp) hh

theorem nextBoundary (count initialList suffix joined tail value : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count initialList)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined initialList suffix)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode tail suffix)))
 (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode value tail))) :
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value (suc count) joined)) := by
 have hp := OriginalResultStackPartitionProof.actualPartition body alpha Delta count initialList suffix joined hl ha
 have hd := InternalRawListRecursionSupportProof.dropNext tail suffix count joined
   (InternalApplicationStepPeelSupportProof.andRight hp) ht
 exact InternalRawListRecursionSupportProof.lookupValue value (suc count) joined tail hd hh

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackSlotsBoundaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackSlotsBoundaryProof
