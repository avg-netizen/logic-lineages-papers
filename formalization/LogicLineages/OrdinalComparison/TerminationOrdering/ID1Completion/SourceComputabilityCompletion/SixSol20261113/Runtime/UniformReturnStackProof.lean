module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackOldSuffixProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.AppendReassociationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionCancellationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnStackProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof (outputTransport)
open InternalArithmeticProgramsSupportProof (additionValue)
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- The complete actual produced row is popped, independently of its values
and of every old result background. The original selector adds deletions first. -/
theorem oldSuffix (children deletions produced old results : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (add children deletions) produced)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results produced old))) :
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryResultStackProgram.oldSuffix old children deletions results)) := by
 obtain ⟨hp⟩ := OriginalResultStackPartitionProof.actualPartition body alpha Delta
   (add children deletions) produced old results hl ha
 have hadd : Nonempty (Derivation body Delta
   (graph2 InternalArithmeticPrograms.addition (add children deletions) deletions children)) :=
   outputTransport InternalArithmeticPrograms.addition (add deletions children) (add children deletions)
     (Fin.cons deletions (Fin.cons children Fin.elim0))
     ⟨InternalAdditionCancellationProof.commutativity deletions children⟩
     (additionValue deletions children)
 exact OriginalResultStackOldSuffixProof.atTotal children deletions results
   (add children deletions) old hadd ⟨Derivation.conjunctionRight hp⟩
/-- An actual deletion prefix remains the same when the inherited old stack is
appended after the remaining child row. No equality of result values is assumed. -/
theorem deletionFront (deletions front childRow produced old childOld results : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions front)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced front childRow)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append childOld childRow old)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results produced old))) :
 Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.front front deletions results)) := by
 have hj := SixSol20261112.Runtime.AppendReassociationProof.appendReassociation
   body alpha Delta front childRow old produced childOld results hp hc ha
 obtain ⟨h⟩ := OriginalResultStackPartitionProof.actualPartition body alpha Delta
   deletions front childOld results hl hj
 exact ⟨Derivation.conjunctionLeft h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnStackProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnStackProof
