module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackOldSuffixTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackSlotsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackOldSuffixProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof (projectionValue outputTransport)
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalArithmeticProgramsSupportProof
open OriginalResultStackSlotsSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem atTotal (children count stack total old : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (graph2 InternalArithmeticPrograms.addition total count children)))
 (hd : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.drop old total stack))) :
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryResultStackProgram.oldSuffix old children count stack)) := by
 let xs : Fin 3 → OTerm alpha := ![children,count,stack]
 have ht : Nonempty (Derivation body Delta (graph3 OriginalHereditaryResultStackProgram.totalCount total children count stack)) :=
  binaryValue InternalArithmeticPrograms.addition (.projection 1) (.projection 0) total count children xs ha (projectionValue 1 xs) (projectionValue 0 xs)
 exact binaryValue InternalRawListRecursion.drop OriginalHereditaryResultStackProgram.totalCount (.projection 2)
  old total stack xs hd ht (projectionValue 2 xs)
theorem prefixDrop (count row reversed suffix stack : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count row)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse reversed row)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append stack reversed suffix))) :
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.drop suffix count stack)) := by
 obtain ⟨laws⟩ := OriginalReverseLengthInvolutionProof.actualLaws body alpha Delta row count reversed hl hr
 obtain ⟨part⟩ := OriginalResultStackPartitionProof.actualPartition body alpha Delta count reversed suffix stack ⟨Derivation.conjunctionLeft laws⟩ ha
 exact ⟨Derivation.conjunctionRight part⟩
theorem children0 : OriginalResultStackOldSuffixTargets.Children0 := by
 intro body alpha Delta count row reversed old stack hl hr ha
 have hz : Nonempty (Derivation body Delta (graph2 InternalArithmeticPrograms.addition count count z)) :=
  outputTransport InternalArithmeticPrograms.addition (InternalAdditionLawsProof.add count z) count
   (Fin.cons count (Fin.cons z Fin.elim0)) ⟨addZero count⟩ (additionValue count z)
 exact atTotal z count stack count old hz (prefixDrop count row reversed old stack hl hr ha)
theorem children1 : OriginalResultStackOldSuffixTargets.Children1 := by
 intro body alpha Delta count row reversed old stack suffix value hl hr ha hc
 have hd := prefixDrop count row reversed suffix stack hl hr ha
 have ht := InternalRawListRecursionSupportProof.consTail suffix value old hc
 exact atTotal (suc z) count stack (suc count) old (additionOne count)
  (InternalRawListRecursionSupportProof.dropNext old suffix count stack hd ht)
theorem children2 : OriginalResultStackOldSuffixTargets.Children2 := by
 intro body alpha Delta count row reversed old stack suffix tail first second hl hr ha hc1 hc2
 have hd := prefixDrop count row reversed suffix stack hl hr ha
 have hd1 := InternalRawListRecursionSupportProof.dropNext tail suffix count stack hd
  (InternalRawListRecursionSupportProof.consTail suffix second tail hc1)
 have hd2 := InternalRawListRecursionSupportProof.dropNext old tail (suc count) stack hd1
  (InternalRawListRecursionSupportProof.consTail tail first old hc2)
 exact atTotal (suc (suc z)) count stack (suc (suc count)) old (additionTwo count) hd2
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackOldSuffixProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackOldSuffixProof
