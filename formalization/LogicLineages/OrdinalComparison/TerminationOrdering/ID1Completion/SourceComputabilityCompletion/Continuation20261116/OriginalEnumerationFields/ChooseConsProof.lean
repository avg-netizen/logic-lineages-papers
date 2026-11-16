module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChooseConsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open OriginalRawSyntaxTransportEvaluationSupportProof InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open InternalAcceptanceCalibrationProof
open Continuation20261115
open SourceProof ListNativeProof LayerSupportProof RecombinationProof

theorem value (n : Nat) (typ : Ty) (a rest : Code (Fin n)) (b param : Nat) (answers : List Nat) :
    evaluate (choose n) (ofFn ![Nat.pair (codeNumber ((.argumentsCons typ a rest) : Code (Fin n))) b,numbersNumber answers,param]) =
      nodeValue (n := n) (rawTypes param) (rawHeads n param) (rawLabels param) (rawTupleBound param) b answers (.argumentsCons typ a rest) := by
  have hlt (a d : Nat) : evaluate InternalLessThan.ltTest (a ::ᵥ d ::ᵥ nil) = if a < d then 1 else 0 :=
    InternalLessThanEvaluationProof.exactLessThanEvaluation a d
  have hg (a d c : Nat) : (a ::ᵥ d ::ᵥ c ::ᵥ nil).get 2 = c := rfl
  have hf (key par : Nat) : evaluate firstAnswer (key ::ᵥ numbersNumber answers ::ᵥ par ::ᵥ nil) = answers[0]?.getD 0 :=
    firstAnswerValue key par answers
  have hs (key par : Nat) : evaluate secondAnswer (key ::ᵥ numbersNumber answers ::ᵥ par ::ᵥ nil) = answers[1]?.getD 0 :=
    secondAnswerValue key par answers
  simp [hlt,hg,hf,hs,choose,evalBranch,sameOfEvaluation,constantEvaluation,
      tag,raw,keyRaw,payload,bound,keyBound,types,heads,labels,tupleBound,
      leftOfEvaluation,rightOfEvaluation,projectionEvaluation,Nat.unpair_pair,codeNumber,
      variableBranch,lambdaBranch,binaryBranch,bottomBranch,ordinaryBranch,numberedBranch,
      numberedLabel,numberedHead,numberedType,numberedTypes,
      bothValue,typeMemberValue,headMemberValue,firstAnswerValue,secondAnswerValue,
      lessCompositionEvaluation,succOfEvaluation,unaryCompositionEvaluation,
      binaryCompositionEvaluation,typesLength,typesAll,
      nodeValue,rawTypes,rawHeads,rawLabels,rawTupleBound,convertedList,andN,Nat.lt_succ_iff,InternalLessThanEvaluationProof.exactLessThanEvaluation]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChooseConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChooseConsProof
