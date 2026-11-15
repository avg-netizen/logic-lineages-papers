module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecPrimrecSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof NumberedMultisetNumericTotalityProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof OriginalRawSyntaxTransportSelectorProof
open InternalApplicationCertificateConstructorsEvaluationProof InternalAcceptanceCalibrationProof
open Continuation20261114

def headValue (code : Nat) : Nat :=
  if (Nat.unpair code).1 = 5 then (Nat.unpair (Nat.unpair (Nat.unpair code).2).2).1
  else (Nat.unpair (Nat.unpair code).2).1

theorem rawValue (table code : Nat) : evaluate raw (ofFn ![table,code]) = code := rfl

theorem headFieldValue (table code : Nat) : evaluate headField (ofFn ![table,code]) = headValue code := by
  simp only [headField,evalBranch,sameOfEvaluation,tag,payload,leftOfEvaluation,rightOfEvaluation,
    constantEvaluation,rawValue,headValue]
  split_ifs <;> simp_all

theorem childValue (child : Program 2) (xs : List Nat) (code : Nat) :
    evaluate (childAt child) (ofFn ![numbersNumber xs,code]) =
    (NumberedCodeParserTable.lookup (xs.map (fun v => v == 1))
      (evaluate child (ofFn ![numbersNumber xs,code]))).toNat := by
  rw [childAt,sameOfEvaluation,constantEvaluation]
  change (if evaluate InternalRawListRecursion.lookup (ofFn ![
    evaluate child (ofFn ![numbersNumber xs,code]),numbersNumber xs]) = 1 then 1 else 0) = _
  rw [InternalEqualityTestEvaluationProof.vectorTwo,ExchangeAnswerSlots.NativeProof.lookupEncoded]
  change (if xs.getD (evaluate child (ofFn ![numbersNumber xs,code])) 0 = 1 then 1 else 0) =
    ((xs.map (fun v => v == 1)).getD (evaluate child (ofFn ![numbersNumber xs,code])) false).toNat
  rw [ExchangeAnswerSlots.NativeProof.boolGet,Bool.beq_eq_decide_eq]
  split_ifs <;> simp_all

theorem firstValue (xs : List Nat) (code : Nat) : evaluate firstAccepted (ofFn ![numbersNumber xs,code]) =
    (NumberedCodeParserTable.lookup (xs.map (fun v => v == 1)) (OriginalRawSyntaxTransport.firstValue code)).toNat := by
  rw [firstAccepted,childValue,firstField,firstOfEvaluation,rawValue]

theorem secondValue (xs : List Nat) (code : Nat) : evaluate secondAccepted (ofFn ![numbersNumber xs,code]) =
    (NumberedCodeParserTable.lookup (xs.map (fun v => v == 1)) (OriginalRawSyntaxTransport.secondValue code)).toNat := by
  rw [secondAccepted,childValue,secondField,secondOfEvaluation,rawValue]

theorem headAcceptedValue (n : Nat) (xs : List Nat) (code : Nat) :
    evaluate (headAccepted n) (ofFn ![numbersNumber xs,code]) =
      (NumberedNumericDecoding.decodeHeadNumber n (headValue code)).isSome.toNat := by
  change evaluate (OriginalHeadDecoderValidity.check n) (ofFn ![evaluate headField (ofFn ![numbersNumber xs,code])]) = _
  rw [headFieldValue,OriginalHeadDecoderValidity.NativeProof.nativeDecoderValidity]

theorem bothValue (xs : List Nat) (code : Nat) : evaluate bothChildren (ofFn ![numbersNumber xs,code]) =
    (NumberedCodeParserTable.lookup (xs.map (fun v => v == 1)) (OriginalRawSyntaxTransport.firstValue code) &&
      NumberedCodeParserTable.lookup (xs.map (fun v => v == 1)) (OriginalRawSyntaxTransport.secondValue code)).toNat :=
  OriginalHeadMove.NativeProof.conjunctionBool _ _ _ _ _ (firstValue xs code) (secondValue xs code)

theorem ordinaryValue (n : Nat) (xs : List Nat) (code : Nat) : evaluate (ordinary n) (ofFn ![numbersNumber xs,code]) =
    ((NumberedNumericDecoding.decodeHeadNumber n (headValue code)).isSome &&
      NumberedCodeParserTable.lookup (xs.map (fun v => v == 1)) (OriginalRawSyntaxTransport.firstValue code)).toNat :=
  OriginalHeadMove.NativeProof.conjunctionBool _ _ _ _ _ (headAcceptedValue n xs code) (firstValue xs code)

theorem numberedValue (n : Nat) (xs : List Nat) (code : Nat) : evaluate (numbered n) (ofFn ![numbersNumber xs,code]) =
    (((NumberedNumericDecoding.decodeHeadNumber n (headValue code)).isSome &&
      NumberedCodeParserTable.lookup (xs.map (fun v => v == 1)) (OriginalRawSyntaxTransport.firstValue code)) &&
      NumberedCodeParserTable.lookup (xs.map (fun v => v == 1)) (OriginalRawSyntaxTransport.secondValue code)).toNat :=
  OriginalHeadMove.NativeProof.conjunctionBool _ _ _ _ _ (ordinaryValue n xs code) (secondValue xs code)

theorem chooseValue (k table code : Nat) (yes no : Program 2) :
    evaluate (choose k yes no) (ofFn ![table,code]) =
      if (Nat.unpair code).1 = k then evaluate yes (ofFn ![table,code]) else evaluate no (ofFn ![table,code]) := by
  simp only [choose,evalBranch,sameOfEvaluation,tag,leftOfEvaluation,rawValue,constantEvaluation]
  split_ifs <;> simp_all

theorem typesSome (value : Nat) : (NumberedNumericDecoding.decodeTypes value).isSome = true := by
  obtain ⟨xs,hxs⟩ := decoderTotality value
  rw [NumberedTypeCodecPrimrecSupportProof.decoderCalibration,hxs]
  rfl

theorem stepValue (n : Nat) (xs : List Nat) (code : Nat) :
    evaluate (step n) (ofFn ![numbersNumber xs,code]) =
      (NumberedCodeParserTable.codeNext n (xs.map (fun v => v == 1)) code).toNat := by
  rcases hp : Nat.unpair code with ⟨t,v⟩
  rcases t with _ | _ | _ | _ | _ | _ | _ | _ | t
  all_goals simp [step,chooseValue,firstValue,secondValue,bothValue,ordinaryValue,numberedValue,
    constantEvaluation,sameOfEvaluation,payload,rightOfEvaluation,rawValue,
    NumberedCodeParserTable.codeNext,NumberedTypeCodecPrimrecSupportProof.decodeTypeExact,typesSome,
    OriginalRawSyntaxTransport.firstValue,OriginalRawSyntaxTransport.secondValue,tagValue,payloadValue,
    headValue,hp]
  all_goals split_ifs <;> simp_all

theorem nativeCodeNext : Targets.NativeCodeNext := by
  intro n table code
  obtain ⟨xs,hxs⟩ := decoderTotality table
  have he := numbersSound table xs hxs
  rw [← he,stepValue,NumberedMultisetNumericSupportProof.numbersRoundTrip]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.NativeProof
