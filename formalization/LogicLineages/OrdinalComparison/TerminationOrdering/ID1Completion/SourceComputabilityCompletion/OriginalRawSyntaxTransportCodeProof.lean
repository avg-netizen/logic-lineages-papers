module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportNativeRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportCodeProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedAuxiliaryShift
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportSemanticProof
open OriginalRawSyntaxTransportNativeRecurrenceProof OriginalRawSyntaxTransportBoundedProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

 theorem semanticShift {n : Nat} (q : Code (Fin n)) (cutoff : Nat) :
    semanticFold .shift 0 cutoff (codeNumber q) = codeNumber (shiftCode cutoff q) := by
  induction q generalizing cutoff <;> rw [semanticEquation] <;>
    simp_all [codeNumber, arityValue, tagValue, payloadValue, firstValue, secondValue,
      leafValue, rebuildValue, shiftCode, shiftVariable]

 theorem semanticErasure {n : Nat} (q : Code (Fin n)) (sigma : Ty) (cutoff : Nat) :
    semanticFold .erase (typeNumber sigma) cutoff (codeNumber q) = codeNumber (eraseCode sigma cutoff q) := by
  induction q generalizing cutoff <;> rw [semanticEquation] <;>
    simp_all [codeNumber, arityValue, tagValue, payloadValue, firstValue, secondValue,
      leafValue, rebuildValue, eraseCode]
  all_goals split_ifs <;> rfl

 theorem semanticRank {n : Nat} (q : Code (Fin n)) (d k : Nat) :
    semanticFold .rank d k (codeNumber q) = codeVariableCount q := by
  induction q generalizing d k <;> rw [semanticEquation] <;>
    simp_all [codeNumber, arityValue, tagValue, payloadValue, firstValue, secondValue,
      leafValue, rebuildValue, codeVariableCount]

 theorem shiftEvaluation (v : List.Vector Nat 2) :
    evaluate shiftRaw v = foldValue .shift 0 (v.get 0) (v.get 1) := by
  rw [shiftRaw, ternaryCompositionEvaluation, foldEvaluation]
  rfl

 theorem eraseEvaluation (v : List.Vector Nat 3) :
    evaluate eraseRaw v = foldValue .erase (v.get 0) (v.get 1) (v.get 2) := foldEvaluation .erase v

 theorem rankEvaluation (v : List.Vector Nat 1) :
    evaluate variableRankRaw v = foldValue .rank 0 0 (v.get 0) := by
  rw [variableRankRaw, ternaryCompositionEvaluation, foldEvaluation]
  rfl

 theorem actualRawSyntaxCodeCalibration : OriginalRawSyntaxTransportTargets.ActualRawSyntaxCodeCalibration := by
  refine ⟨?_, ?_, ?_⟩
  · intro n cutoff q
    rw [shiftEvaluation, foldSemantic]
    exact semanticShift q cutoff
  · intro n cutoff sigma q
    rw [eraseEvaluation, foldSemantic]
    exact semanticErasure q sigma cutoff
  · intro n q
    rw [rankEvaluation, foldSemantic]
    exact semanticRank q 0 0

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportCodeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportCodeProof
