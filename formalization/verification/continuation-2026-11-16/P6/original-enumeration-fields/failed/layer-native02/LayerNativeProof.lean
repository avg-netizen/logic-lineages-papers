module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerNativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open OriginalRawSyntaxTransportEvaluationSupportProof InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open InternalAcceptanceCalibrationProof
open Continuation20261115
open SourceProof ListNativeProof LayerSupportProof RecombinationProof

theorem chooseValue (n : Nat) (c : Code (Fin n)) (b param : Nat) (answers : List Nat) :
    evaluate (choose n) (ofFn ![Nat.pair (codeNumber c) b,numbersNumber answers,param]) =
      nodeValue (rawTypes param) (rawHeads n param) (rawLabels param) (rawTupleBound param) b answers c := by
  cases c <;>
    simp [choose,evalBranch,sameOfEvaluation,constantEvaluation,
      tag,raw,keyRaw,payload,bound,keyBound,types,heads,labels,tupleBound,
      leftOfEvaluation,rightOfEvaluation,projectionEvaluation,Nat.unpair_pair,codeNumber,
      variableBranch,lambdaBranch,binaryBranch,bottomBranch,ordinaryBranch,numberedBranch,
      numberedLabel,numberedHead,numberedType,numberedTypes,
      bothValue,typeMemberValue,headMemberValue,firstAnswerValue,secondAnswerValue,
      lessCompositionEvaluation,succOfEvaluation,unaryCompositionEvaluation,
      binaryCompositionEvaluation,typesLength,typesAll,
      nodeValue,rawTypes,rawHeads,rawLabels,rawTupleBound,convertedList,andN,Nat.lt_succ_iff]

attribute [local irreducible] choose OriginalCodeValidityGuard.check

theorem guardValue (n key param : Nat) (answers : List Nat) :
    evaluate (.composition (OriginalCodeValidityGuard.check n) ![raw])
      (ofFn ![key,numbersNumber answers,param]) =
        (NumberedNumericDecoding.decodeCode n (Nat.unpair key).1).isSome.toNat := by
  change evaluate (OriginalCodeValidityGuard.check n) (ofFn ![(Nat.unpair key).1]) = _
  rw [OriginalCodeValidityGuard.NativeProof.nativeValidity]
  rfl

theorem layerValue (n key param : Nat) (answers : List Nat) :
    evaluate (layer n) (ofFn ![key,numbersNumber answers,param]) =
      Encodable.encode (recombination n key param answers) := by
  rw [layer,succOfEvaluation,bothValue,guardValue]
  cases hc : NumberedNumericDecoding.decodeCode n (Nat.unpair key).1 with
  | none => simp [recombination,hc]
  | some c =>
    have he := NumberedNumericDecodingProof.codeNumericSound n (Nat.unpair key).1 c hc
    have hk : Nat.pair (codeNumber c) (Nat.unpair key).2 = key := by
      rw [he]
      exact Nat.pair_unpair key
    have hv : evaluate (choose n) (ofFn ![key,numbersNumber answers,param]) =
        nodeValue (rawTypes param) (rawHeads n param) (rawLabels param) (rawTupleBound param) (Nat.unpair key).2 answers c := by
      conv_lhs => rw [← hk]
      exact chooseValue n c (Nat.unpair key).2 param answers
    simp [hc,recombination,hv]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerNativeProof
