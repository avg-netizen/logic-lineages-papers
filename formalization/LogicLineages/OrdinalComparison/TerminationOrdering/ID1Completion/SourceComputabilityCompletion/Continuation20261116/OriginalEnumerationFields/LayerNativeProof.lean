module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChooseVarProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChooseLamProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChooseAppProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChooseBottomProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChooseOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChooseNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChooseNilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChooseConsProof
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
  cases c with
  | var index => exact ChooseVarProof.value n index b param answers
  | lam typ child => exact ChooseLamProof.value n typ child b param answers
  | app typ a bcode => exact ChooseAppProof.value n typ a bcode b param answers
  | bottom typ => exact ChooseBottomProof.value n typ b param answers
  | ordinary head child => exact ChooseOrdinaryProof.value n head child b param answers
  | numbered label head typ child ts args => exact ChooseNumberedProof.value n label head typ child ts args b param answers
  | argumentsNil  => exact ChooseNilProof.value n  b param answers
  | argumentsCons typ a rest => exact ChooseConsProof.value n typ a rest b param answers

attribute [local irreducible] choose OriginalCodeValidityGuard.check

theorem guardValue (n key param : Nat) (answers : List Nat) :
    evaluate (.composition (OriginalCodeValidityGuard.check n) ![raw])
      (ofFn ![key,numbersNumber answers,param]) =
        (NumberedNumericDecoding.decodeCode n (Nat.unpair key).1).isSome.toNat := by
  change evaluate (OriginalCodeValidityGuard.check n)
    (ofFn (fun i : Fin 1 => evaluate (![raw] i) (ofFn ![key,numbersNumber answers,param]))) = _
  have he : (fun i : Fin 1 => evaluate (![raw] i) (ofFn ![key,numbersNumber answers,param])) =
      ![(Nat.unpair key).1] := by
    funext i
    obtain rfl := Fin.eq_zero i
    simp [raw,keyRaw,leftOfEvaluation,projectionEvaluation]
  rw [he,OriginalCodeValidityGuard.NativeProof.nativeValidity]

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
    simpa [hc,recombination] using hv
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerNativeProof
